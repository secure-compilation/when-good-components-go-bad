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

(* Main simulation theorem. *)
Section Recomposition.
  Variables p c p' c' : program.

  Hypothesis Hwfp  : well_formed_program p. 
  Hypothesis Hwfc  : well_formed_program c. 
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).
  Hypothesis Hprog_is_closed' : closed_program (program_link p' c').

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p'  c'.
  Let prog'' := program_link p c'.

  Let state := @Symbolic.state mt LRC.lrc_tags [eqType of unit].
  Let genvtype := unit.
  Let step1 := (fun (ge: genvtype) s t s' => match t with
                                       | [::] => step_me s s' None
                                       | e :: [::] => step_me s s' (Some e)
                                       | _ => False
                                       end).
  Let step2 := (fun (ge: genvtype) s t s' => match t with
                                       | [::] => step_mp s s' None
                                       | e :: [::] => step_mp s s' (Some e)
                                       | _ => False
                                       end).
  Definition initial_state1: state -> Prop :=
    fun s => s = initial_state (code prog  ) (prog_buffers prog  ) (prog_interface prog  ). 

  Definition initial_state2: state -> Prop :=
    fun s => s = initial_state (code prog' ) (prog_buffers prog' ) (prog_interface prog' ). 

  Definition initial_state3: state -> Prop :=
    fun s => s = initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'').
  
  Definition color_of: state -> Component.id :=
    fun '(Symbolic.State m r (Types.Atom _ tpc) _ _) =>
      match (tpc) with
      | Level _ c => c
      end.
  
  Definition allowed_UB: state -> Prop :=
    fun s => (color_of s) \in (domm ic).

  Definition final_state_me: state -> Prop :=
    fun '(Symbolic.State m r (Types.Atom pc _) _ _) =>
      match (m pc) with
      | None => False
      | Some (Types.Atom i tag) =>
          ((Types.decode_instr i) = Some (Types.Halt _)) /\ (is_code tag = true)
      end.
  
  Definition final_state_rUB: state -> Prop :=
    fun '(Symbolic.State m r (Types.Atom pc tpc) _ _) =>
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
    
    Definition well_formed_metadata (i : side) (m: metadata) mem mem' : Prop :=
      forall v1 v2 v3 v c off,
        In (v1, v2, v3, c) m ->
        (match i with Left => v1 | Right => v2 end) = v ->
        get_offset i c = Some off ->
        points_to_comp_code' i (side_of c) (mem) (Types.vala v) c
        /\ points_to_comp_code (mem') (Types.vala v3) c
        /\ (is_relevant_comp i c -> (Types.vala v3) = addw (Types.vala v) (as_word off)).
    (* todo : sanity check *)


    (* JT: It would be easier to use inductive predicates for the stack invariant. Here's my attempt: *)
    Inductive wf_stack (m1 m2 m3: memory): nat -> stack -> Prop :=
    | wf_stack_empty:
        wf_stack m1 m2 m3 0 []
    | wf_stack_cons_left: forall n st v1 v2 v3 C off,
      forall (SIDE: is_relevant_comp Left C)
        (OFF_C: get_offset Left C = Some off)
        (PTS_CODE1: points_to_comp_code' Right (side_of C) m1 v1 C)
        (PTS_COD22: points_to_comp_code m2 v2 C)
        (PTS_CODE3: points_to_comp_code m3 v3 C)
        (VALA_OFF: v3 = addw v1 (as_word off))
        (WF_ST: wf_stack m1 m2 m3 n st),
        wf_stack m1 m2 m3 (n+1)
          ((Types.Atom v1 (Ret n), Types.Atom v2 (Ret n), Types.Atom v3 (Ret n), C) :: st)
    | wf_stack_cons_right: forall n st v1 v2 v3 C off,
      forall (SIDE: is_relevant_comp Right C)
        (OFF_C: get_offset Right C = Some off)
        (PTS_CODE1: points_to_comp_code' Right (side_of C) m1 v1 C)
        (PTS_COD22: points_to_comp_code m2 v2 C)
        (PTS_CODE3: points_to_comp_code m3 v3 C)
        (VALA_OFF: v3 = addw v2 (as_word off))
        (WF_ST: wf_stack m1 m2 m3 n st),
        wf_stack m1 m2 m3 (n+1)
          ((Types.Atom v1 (Ret n), Types.Atom v2 (Ret n), Types.Atom v3 (Ret n), C) :: st)
    .

    Notation data := (Types.atom (Types.mword mt) mem_tag).
    
    Definition data_match (i: side) (comp: Component.id) (m: metadata) (d: stack_value) (d': stack_value) : Prop :=
      match (d, d') with
      | (Types.Atom v1 t1, Types.Atom v2 t2) =>
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
    
    Definition data_match' (i: side) (m: metadata) (d: data) (d': data) : Prop :=
      match (d, d') with
      | (Types.Atom v1 t1, Types.Atom v2 t2) =>
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

    Variant decode_match (mem: @memory mt) (mem': @memory mt) v v' off c: Prop :=
      | decode_match_no_JAL:
        (forall imm, decode_instr v <> Some (Jal imm)) ->
        (forall imm', decode_instr v' <> Some (Jal imm')) ->
        v = v' ->
        decode_match mem mem' v v' off c
      | decode_match_alloc_JAL:
        decode_instr v  = Some (Jal (word_of_nat alloc_label) ) ->
        decode_instr v' = Some (Jal (word_of_nat alloc_label) ) ->
        decode_match mem mem' v v' off c
      | decode_match_JAL: forall imm imm' d d',
          decode_instr v  = Some (Jal imm ) ->
          decode_instr v' = Some (Jal imm') ->
          mem (swcast imm) = Some d ->
          mem' (swcast imm') = Some d' ->
          is_code (taga d) ->
          taga d = taga d' -> (* exact same tag, so same entry point if there is one *)
          (color (taga d) = c -> imm' = addw imm (as_word off)) ->
          decode_match mem mem' v v' off c
    .

    Definition combined_codes (i: side) (s: state) (s': state) : Prop :=
      forall w v t off c,
        is_relevant_comp i c ->
        get_offset i c = Some off ->
        is_code (t) ->
        color (t) = c ->
        ((mem s w = Some v@t -> exists v', decode_match (mem s) (mem s') v v' off c /\ (mem s' (addw w (as_word off)) = Some v'@t))
         /\ ((mem s' (addw w (as_word off)) = Some (v@t)) -> exists v', decode_match (mem s) (mem s') v' v off c /\ (mem s w = Some (v'@t))))
    .

    Definition end_condition (mem: memory) : Prop :=
      forall w v,
        mem w = Some v ->
        is_code (taga v) ->
        (match (decode_instr (vala v)) with Some Halt => True | _ => False end)
        \/ exists v', (mem (addw w onew) = Some v' /\ is_code (taga v'))
    .

    (* necessary invariants for the allocation case *)
    Definition memory_prefix_condition (mem:memory) nc :=
      forall current_c,
        let prefix := (@component_memory_prefix mt (ssrint.Posz(1 + current_c)) nc) in
        let mask := (@component_memory_prefix mt (ssrint.Posz((2 ^ nc)-1)) nc) in
        let prefix_filter := (fun mw => ((word.andw mw mask) == prefix) ) in
        let comp_filter := (fun w v => andb (color (taga v) == current_c) (negb (is_code (taga v)))) in
        filter prefix_filter (domm (mem)) =
          fsetD (domm (filterm comp_filter (mem))) (domm (initial_memory (prog_buffers prog))).

    Definition code_prefix_condition (mem:memory) nc :=
      forall w v,
        mem w = Some v ->
        is_code (taga v) ->
        let prefix := (@component_memory_prefix mt (ssrint.Posz(0)) nc) in
        let mask := (@component_memory_prefix mt (ssrint.Posz((2 ^ nc)-1)) nc) in
        ((word.andw w mask) == prefix).

    Definition alloc_empty (mem: @memory mt) :=
      mem (word_of_nat alloc_label) = None.

    (* necessary invariants for the JMP and JAL cases *)
    Definition address_correctness w t (mem: memory) :=
      match t with
      | Ret _ | InternalJump => exists (v: atom (mword mt) _), mem w = Some v /\ is_code (taga v)
      | Other | Invalidated => True
      end.

    Definition memory_address_correctness (i: side) (s: state) :=
      forall v w,
        is_relevant_comp i (color (taga v)) ->
         mem s w = Some v ->
         address_correctness (vala v) (vtag (taga v)) (mem s).

    Definition register_address_correctness (s: state) :=
      forall v r,
         regs s r = Some v ->
         address_correctness (vala v) (taga v) (mem s).

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
    
    (* necessary invariant to prove that registers are properly cleared on call/return *)
    Definition register_domm (regs: {fmap reg mt -> atom (mword mt) value_tag} ) : Prop :=
      ((domm regs): seq (reg mt)) = ra :: (map (word_of_nat) reg_list).

    (* necessary invariant on calls that change which state is weakly/strongly related *)
    Definition entry_points_offset i (mem: @memory mt) (mem': @memory mt) : Prop :=
      forall c w w' d d' e,
        is_relevant_comp i c ->
        mem  w  = Some d ->
        mem' w' = Some d' ->
        is_code (taga d ) ->
        is_code (taga d') ->
        color (taga d ) = c ->
        color (taga d') = c ->
        entry (taga d ) = Some e ->
        entry (taga d') = Some e ->
        (exists off,
            get_offset i c = Some off
            /\  w' = addw w (as_word off)).
    
    Definition general_memory_correctness (mem: memory) nc : Prop :=
      memory_prefix_condition mem nc
      /\ code_prefix_condition mem nc
      /\ alloc_empty mem
      /\ BNZ_correctness mem
      /\ end_condition mem
      /\ color_in_memory mem.

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
          general_memory_correctness (mem s1) (comp_num s1) ->
          general_memory_correctness (mem s2) (comp_num s2) ->
          general_memory_correctness (mem s3) (comp_num s3) ->
          combined_codes Left  s1 s3 ->
          combined_codes Right s2 s3 ->
          common_equiv m s1 s2 s3
    .
    Variant strong_equiv (i: side): metadata -> state -> state -> Prop :=
      strong_equiv_def : forall m s s',
          well_formed_metadata i m (mem s) (mem s') ->
          comp_num s = comp_num s' ->
          same_pc i s s' ->
          color_of s = color_of s' ->
          side_of (color_of s) = i ->
          memory_address_correctness i s ->
          memory_address_correctness i s' ->
          entry_points_offset i (mem s) (mem s') ->
          register_address_correctness s ->
          register_address_correctness s' ->
          memory_match i m s s' ->
          registers_match i m s s' ->
          strong_equiv i m s s'
    .

    Variant weak_equiv (i: side): metadata -> state -> state -> Prop :=
      weak_equiv_def : forall m s s',
          well_formed_metadata i m (mem s) (mem s') ->
          comp_num s = comp_num s' ->
          color_of s = color_of s' ->
          side_of (color_of s) = other_side i ->
          memory_address_correctness (other_side i) s ->
          memory_address_correctness (other_side i) s' ->
          entry_points_offset i (mem s) (mem s') ->
          memory_match i m s s' ->
          weak_equiv i m s s'
    .


  End SimulationRelations.

  Notation match_states := (match_states sem sem' sem'' (common_equiv)
    (strong_equiv Left) (strong_equiv Right) (weak_equiv Left) (weak_equiv Right)).

  (*** Tactics ***)

  
  Ltac eq_op_to_eq :=
    let ineq := fresh in
    match goal with
      | H: (true = (?a == ?b)) |- ?a = ?b => 
    eapply (@contraNeq (Ord.eqType _) false); auto; intro ineq; exfalso; try destruct ineq; eapply no_fixpoint_negb; eauto
    end.

  Ltac convert_eq_op :=
    repeat 
    match goal with
    | H: (true = (?a == ?b)) |- _ => assert (a = b) by eq_op_to_eq; (subst a || subst b); clear H
    end.

  Ltac decode_instr_eq :=
    (match goal with
     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
       => simpl; rewrite <- op; simpl; rewrite inst; try done
     end).
  
  Ltac oapp_False :=
    let b := fresh in
    match goal with | H: oapp _ False ?v |- _ => remember v as b; destruct b; try contradiction; simpl in H; try subst b end.
  
  Ltac unfold_match :=
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
  Ltac unfold_match' H :=
    let a := fresh "a" in
    match (type of H) with
    | (match ?cond as _ return _ with _ => _ end) = _ => try(remember cond as a; destruct a);
                                                       simpl in H; try (inversion H; done)
    | _ = (match ?cond as _ return _ with _ => _ end) => try(remember cond as a; destruct a);
                                                       simpl in H; try (inversion H; done)
    end.
  Ltac unfold_match_misc :=
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
  Ltac unfold_bind :=
    let a := fresh "a" in
    match goal with
    | H : _ = (Option.bind ?f ?v) |- _ => remember v as a; destruct a; simpl in H; try (inversion H; done)
    | H : (Option.bind ?f ?v) = _ |- _ => remember v as a; destruct a; simpl in H; try (inversion H; done)
    | H : match (Option.bind ?f ?v) with _ => _ end |- _ => remember v as a; destruct a; simpl in H; try (inversion H; done)
    end.

  Ltac simplify_some :=
    match goal with
    | H : Some ?a = Some _ |- _ => inversion H; clear H; subst a
    | H : Some (?a, ?b) = Some _ |- _ => inversion H; clear H; try subst a; try subst b
    | H : (?a, ?b) = (_, _) |- _ => inversion H; clear H; try subst a; try subst b
    | H : Some _ = Some ?a |- _ => inversion H; clear H; try subst a
    | H : Some _ = Some (?a, ?b) |- _ => inversion H; clear H; try subst a; try subst b
    | H : (_, _) = (?a, ?b) |- _ => inversion H; clear H; try subst a; try subst b
    end.

  Ltac destruct_unit :=
    match goal with
    | u: unit |- _ => destruct u
    end.

  Ltac updm_to_setm :=
    repeat (match goal with | H: Some ?f = updm _ _ _ |- _ => pose proof (updm_set (esym H)); clear H; subst f end).
  
  Ltac unfold_all :=
    repeat (simpl in *;(simplify_some || unfold_bind || destruct_unit || unfold_match_misc || updm_to_setm)).  
  
  Ltac goal_match_bind_step :=
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

  Ltac deduce_reg reg_match :=
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


  Ltac deduce_equality s_eq :=
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
  
  (*** Equivalence preservation lemmas ***)
  
  Lemma preserves_equiv_left_pc_incr :
    forall s1 s2 s3 M s1' s3' pc1' tpc1' pc3' tpc3',
      strong_equiv Left M s1 s3
      /\ weak_equiv Right M s2 s3
      /\ common_equiv M s1 s2 s3 ->
      s1' = State _ _ (mem s1) (regs s1) (pc1'@tpc1') tt (comp_num s1) ->
      s3' = State _ _ (mem s3) (regs s3) (pc3'@tpc3') tt (comp_num s3) ->
      same_pc Left s1' s3' ->
      tpc1' = taga (pc s1) ->
      tpc3' = taga (pc s3) ->
      strong_equiv Left M s1' s3'
      /\ weak_equiv Right M s2 s3'
      /\ common_equiv M s1' s2 s3'.
  Proof.
    intros s1 s2 s3 M s1' s3' pc1' tpc1' pc3' tpc3' equiv eq_s1' eq_s3' pc1'_pc3' pc1_tag pc3_tag.
    destruct equiv as [strong [weak common]].
    split; [|split].
    - destruct strong as [? ? ? wf_m ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
      econstructor; destruct s, s', pc0, pc1; try (subst; intros; auto; done); try congruence.
    - destruct weak as [? ? ? wf_m ? color_eq side_s' s_mem_cor s'_mem_cor entry_off mem_match].
      econstructor; try (rewrite eq_s3'; simpl; auto; done); try (subst; intros; auto; done); try congruence.
      subst. destruct s, s', pc0, pc1. simpl in *. trivial.
    - destruct common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                            [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 col_mem1]]]]]
                            [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 col_mem2]]]]]
                            [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 col_mem3]]]]] code_left code_right].
      eapply common_equiv_def with (n := n) (c := c0);
        try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; try done.
      + rewrite eq_s1'. rewrite pc1_tag. simpl. exact tag_pc1.
      + rewrite eq_s3'. rewrite pc3_tag. simpl. exact tag_pc3.
  Qed.

    
  Lemma preserves_equiv_left_mem_write:
    forall s1 s2 s3 M s1' s3' w v v' m1' m3' i,
      strong_equiv Left M s1 s3
      /\ weak_equiv Right M s2 s3
      /\ common_equiv M s1 s2 s3 ->
      data_match' Left M v v' ->
      (color (taga v)) = (color (taga v')) ->
      (color (taga v)) = color_of s1 ->
      is_relevant_comp Left (color (taga v)) ->
      (forall v', (mem s1 w) = Some v' \/ (mem s3 w) = Some v' -> (color (taga v)) = (color (taga v'))) -> 
      (exists d, mem s3 w = Some d /\ not (is_code (taga d))) ->
      (exists d, mem s1 w = Some d /\ not (is_code (taga d))) ->
      mem s1 (vala (pc s1)) = Some i ->
      is_code (taga i) ->
      not (is_code (taga v)) ->
      not (is_code (taga v')) ->
      address_correctness (vala v) (vtag (taga v)) (mem s1) ->
      address_correctness (vala v') (vtag (taga v')) (mem s3) ->
      updm (mem s1) w v = Some m1' ->
      updm (mem s3) w v' = Some m3' ->
      s1' = State _ _ m1' (regs s1) (pc s1) tt (comp_num s1) ->
      s3' = State _ _ m3' (regs s3) (pc s3) tt (comp_num s3) ->
      strong_equiv Left M s1' s3'
      /\ weak_equiv Right M s2 s3'
      /\ common_equiv M s1' s2 s3'.
  Proof.
    intros s1 s2 s3 M s1' s3' w v v' m1' m3' i equiv v_match v_color M_color v_relevant same_color no_code_w_s3 no_code_w_s1
      i_is_pc code_i no_code_v no_code_v' correct_v correct_v' eq_m1 eq_m3 eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    pose proof (updm_set eq_m1). pose proof (updm_set eq_m3). subst m1' m3'.
    split; [|split].
    - destruct strong as [? ? ? wf_m ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match];
      econstructor; destruct s, s', pc0, pc1; try (rewrite eq_s1' eq_s3'; simpl; auto; done); try congruence.
      + intros ? ? ? ? comp ? in_m veq off_eq. subst v0. unfold mem. rewrite eq_s1' eq_s3'. simpl.
        unfold points_to_comp_code, points_to_comp_code'. rewrite setmE. rewrite setmE. split; [|split].
        * remember (@eq_op (Ord.eqType _) (Types.vala v1) w) as cond. destruct cond.
          -- assert (eq: Types.vala v1 = w) by eq_op_to_eq.
            pose proof (wf_m _ _ _ v1 _ off in_m) as conj. simpl in conj.
            destruct (conj) as [points_s [points_s' off_cond]]; auto.
            unfold points_to_comp_code' in points_s. rewrite eq in points_s. simpl.
            oapp_False. destruct points_s as [comp_eq disj].
            rewrite (same_color a); auto. split; auto. destruct disj as [[? ?] | ?]; inversion H0.
            exfalso. destruct no_code_w_s1 as [d [d_eq d_nocode]]. rewrite d_eq in HeqH0. simplify_some. done.
          -- eapply wf_m; eauto.
        * remember (@eq_op (Ord.eqType _) (Types.vala v3) w) as cond. destruct cond.
          -- assert (eq: Types.vala v3 = w) by eq_op_to_eq.
            pose proof (wf_m _ _ _ v1 _ off in_m) as conj. simpl in conj.
            destruct (conj) as [points_s [points_s' off_cond]]; auto.
            unfold points_to_comp_code in points_s'. simpl.
            oapp_False. destruct points_s' as [comp_eq code]. rewrite <- v_color.
            rewrite (same_color a); auto. split; auto.
            exfalso. destruct no_code_w_s3 as [d [d_eq d_nocode]]. rewrite eq d_eq in HeqH0. simplify_some. done.
            right. rewrite <- eq. done.
          -- eapply wf_m; eauto.
        * intro comp_in_ip. eapply (wf_m _ _ _ _ _ _ in_m); auto.
      + destruct common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                            [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 col_mem1]]]]]
                            [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 col_mem2]]]]]
                            [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 col_mem3]]]]] code_left code_right].
        destruct pc_s1_s3 as [? ? ? eq_none|? ? ? ? eq_comp eq_off pc_s1_s3].
        * eapply same_pc_alloc; try rewrite eq_s1'; try rewrite eq_s3'; simpl; auto.
          rewrite setmE.
          remember (@eq_op (Ord.eqType _) (Types.vala (pc s)) w) as cond. simpl in *. rewrite <- Heqcond.
          destruct cond; simpl; auto.
          exfalso. assert (eqw: Types.vala (pc s) = w) by eq_op_to_eq. subst w.
          destruct no_code_w_s1 as [d [d_eq d_nocode]]. rewrite d_eq in eq_none. done.
        * eapply same_pc_normal; eauto.
          -- subst s1'. simpl. rewrite setmE. remember (@eq_op (Ord.eqType _) (Types.vala (pc s)) w) as cond. simpl in *.
             rewrite i_is_pc. rewrite <- Heqcond. eapply (@eq_trans _ _ (Some (if cond then v else i))).
             destruct cond; trivial. subst cond. reflexivity.
          -- subst s1'. destruct s, pc0. simpl in *. exact eq_off.
          -- rewrite eq_s1' eq_s3'. simpl. done.
      + subst. trivial.
      + subst. intros d w' rel deq. simpl. destruct d as [vd [vt ? ? ?]]. simpl.
        remember (@eq_op (Ord.eqType _) w' w) as cond. 
        remember (@eq_op (Ord.eqType _) vd w) as cond1.
        simpl in *. rewrite setmE in deq. rewrite <- Heqcond in deq.
        destruct cond; destruct vt; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond1; destruct cond1;
          convert_eq_op; try (simplify_some; simpl in *; auto).
        all: try (destruct correct_v as [? [eq1 ?]]; destruct no_code_w_s1 as [? [eq2 ?]];
                  rewrite eq1 in eq2; simplify_some; contradiction).
        all: try (rewrite M_color; done).
        all: try eapply (s_mem_cor _ w' _ deq).
        all: try (eapply modusponens; [eapply (s_mem_cor _ w' _ deq) | ]; simpl; intros [v'' [v''eq v''code]]; 
                  destruct no_code_w_s1 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some;
              (contradiction || (destruct v''code; contradiction))).
      + subst. intros d w' rel deq. simpl. destruct d as [vd [vt ? ? ?]]. simpl.
        remember (@eq_op (Ord.eqType _) w' w) as cond. 
        remember (@eq_op (Ord.eqType _) vd w) as cond1.
        simpl in *. rewrite setmE in deq. rewrite <- Heqcond in deq.
        destruct cond; destruct vt; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond1; destruct cond1;
          convert_eq_op; try (simplify_some; simpl in *; auto).
        all: try (destruct correct_v' as [? [eq1 ?]]; destruct no_code_w_s3 as [? [eq2 ?]];
                  rewrite eq1 in eq2; simplify_some; contradiction).
        all: try (rewrite <- v_color; rewrite M_color; done).
        all: try eapply (s'_mem_cor _ w' _ deq).
        all: try (eapply modusponens; [eapply (s'_mem_cor _ w' _ deq) | ]; simpl; intros [v'' [v''eq v''code]]; 
                  destruct no_code_w_s3 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some;
              (contradiction || (destruct v''code; contradiction))).
      + subst. simpl. intros col w' w'' d d' e rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq.
        rewrite setmE in eqw'. rewrite setmE in eqw''.
        unfold_match' eqw'; try convert_eq_op; try simplify_some; try contradiction.
        unfold_match' eqw''; try convert_eq_op; try simplify_some; try contradiction.
        eapply (entry_off); eauto.
      + subst. intros d w' deq. simpl. destruct d as [vd vt].
        remember (@eq_op (Ord.eqType _) vd w) as cond.
        destruct vt; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond; destruct cond;
          convert_eq_op;
          try eapply (s_reg_cor _ w' deq);
          try (eapply modusponens; [eapply (s_reg_cor _ w' deq) | ]; simpl; intros [v'' [v''eq v''code]];
               destruct no_code_w_s1 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some;
               (contradiction || (destruct v''code; contradiction))).
      + subst. intros d w' deq. simpl. destruct d as [vd vt].
        remember (@eq_op (Ord.eqType _) vd w) as cond.
        destruct vt; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond; destruct cond;
          convert_eq_op;
          try eapply (s'_reg_cor _ w' deq);
          try (eapply modusponens; [eapply (s'_reg_cor _ w' deq) | ]; simpl; intros [v'' [v''eq v''code]];
               destruct no_code_w_s3 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some;
              (contradiction || (destruct v''code; contradiction))).
      + unfold memory_match in *. rewrite eq_s1' eq_s3'. simpl.
        intros. 
        rewrite setmE. rewrite setmE.
        remember (@eq_op (Ord.eqType _) w0 w) as cond. destruct cond.
        * split; intro eq; inv eq; eexists; split; eauto.
        * apply mem_match; auto.
    - destruct weak as [? ? ? wf_m ? color_eq side_s' s_mem_cor s'_mem_cor entry_off mem_match];
      econstructor; destruct s, s', pc0, pc1; subst; auto.
      + intros ? ? ? ? comp ? in_m veq off_eq. subst v0. simpl.
        unfold points_to_comp_code. rewrite setmE. split; [|split].
        * remember (@eq_op (Ord.eqType _) (Types.vala v1) w) as cond. destruct cond.
          -- assert (eq: Types.vala v1 = w) by eq_op_to_eq.
             pose proof (wf_m _ _ _ v2 _ off in_m) as conj. simpl in conj.
             destruct (conj) as [points_s [points_s' off_cond]]; auto.
          -- eapply wf_m; eauto.
        * remember (@eq_op (Ord.eqType _) (Types.vala v3) w) as cond. destruct cond.
          -- assert (eq: Types.vala v3 = w) by eq_op_to_eq.
             pose proof (wf_m _ _ _ v2 _ off in_m) as conj. simpl in conj.
             destruct (conj) as [points_s [points_s' off_cond]]; auto.
             unfold points_to_comp_code in points_s'. simpl.
            oapp_False. destruct points_s' as [comp_eq code]. rewrite <- v_color.
            rewrite (same_color a); auto. split; auto.
            exfalso. destruct no_code_w_s3 as [d [d_eq d_nocode]]. rewrite eq d_eq in HeqH0. simplify_some. done.
            right. rewrite <- eq. done.
          -- eapply wf_m; eauto.
        * intro comp_in_ip. eapply (wf_m _ _ _ _ _ _ in_m); auto.
      + subst. intros d w' rel deq. simpl. destruct d as [vd [vt ? ? ?]]. simpl.
        remember (@eq_op (Ord.eqType _) w' w) as cond. 
        remember (@eq_op (Ord.eqType _) vd w) as cond1.
        simpl in *. rewrite setmE in deq. rewrite <- Heqcond in deq.
        destruct cond; destruct vt; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond1; destruct cond1;
          convert_eq_op; try (simplify_some; simpl in *; auto);
          try (destruct correct_v' as [? [eq1 ?]]; destruct no_code_w_s3 as [? [eq2 ?]]; rewrite eq1 in eq2; simplify_some;contradiction).
        all: try eapply (s'_mem_cor _ w' _ deq).
        all: try (eapply modusponens; [eapply (s'_mem_cor _ w' _ deq) | ]; simpl; intros [v'' [v''eq v''code]];
               destruct no_code_w_s3 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some;
              (contradiction || (destruct v''code; contradiction))).
      + subst. simpl. intros col w' w'' d d' e rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq.
        rewrite setmE in eqw''.
        unfold_match' eqw''; try convert_eq_op; try simplify_some; try contradiction.
        eapply (entry_off); eauto.
      + unfold memory_match in *. simpl.
        intros.
        rewrite setmE.
        remember (@eq_op (Ord.eqType _) w0 w) as cond. destruct cond.
        * assert (eq_w: w0 = w) by eq_op_to_eq.
          subst. simpl in *. split; intro eq; inv eq; exfalso.
          -- remember (mem1 w) as v_opt. destruct v_opt as [d'|].
             ++ assert (color (Types.taga d) = color (Types.taga d')) by (rewrite <- v_color; eapply same_color; auto). simpl in v_relevant.
                { eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
                  inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. rewrite <- v_color. auto. }
             ++ simpl in v_relevant. 
                { eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
                  inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. rewrite <- v_color. auto. }
          -- pose proof (mem_match w d H0 H1) as [_ d_impl].
             destruct (d_impl H3) as [d' [d_d'_match eq_d']].
             assert (d'_color: color (Types.taga v) = color (Types.taga d')) by (eapply same_color; auto).
             rewrite d'_color in v_relevant. assert (d'_color_bis: (color (Types.taga d') = color (Types.taga d))).
             { destruct d, d'. simpl. unfold data_match' in d_d'_match. destruct d_d'_match. subst. done. }
             rewrite <- d'_color_bis in H1. simpl in *. 
             { eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
               inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. }
        * apply mem_match; auto.
    - destruct common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                            [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 col_mem1]]]]]
                            [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 col_mem2]]]]]
                            [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 col_mem3]]]]] code_left code_right].
      eapply common_equiv_def with (n := n) (c := c0); 
        try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; try done;
        try (split; [|split; [|split; [|split; [|split]]]]).
      + rewrite eq_s3'. simpl. clear strong weak code_left code_right v_match tag_pc1 tag_pc2 tag_pc3.
        simpl in *. 
        induction wfst; intros.
        * eapply wf_stack_empty; eauto.
        * eapply wf_stack_cons_left; eauto.
          -- rewrite eq_s1'. simpl.
             unfold points_to_comp_code'. rewrite setmE. 
             remember (@eq_op (Ord.eqType _) v1 w) as cond. unfold mt, concrete_int_32_mt, word_size in Heqcond.
             destruct cond; try exact PTS_CODE1.
             assert (eq_w: v1 = w) by eq_op_to_eq. subst v1.
             exfalso. unfold points_to_comp_code' in PTS_CODE1.
             oapp_False.
             destruct PTS_CODE1 as [color_a [[_ side_of_C] | code_a]].
             ++ simpl in SIDE. unfold side_of in *. rewrite SIDE in side_of_C. inv side_of_C.
             ++ destruct no_code_w_s1 as [d [d_eq d_nocode]]. rewrite d_eq in HeqH. simplify_some. done. 
          -- simpl.
             unfold points_to_comp_code. rewrite setmE. 
             remember (@eq_op (Ord.eqType _) v3 w) as cond. unfold mt, concrete_int_32_mt, word_size in Heqcond.
             destruct cond; try exact PTS_CODE3.
             assert (eq_w: v3 = w) by eq_op_to_eq. subst w.
             exfalso. unfold points_to_comp_code in PTS_CODE3.
             oapp_False.
             destruct PTS_CODE3 as [color_a code_a].
              destruct no_code_w_s3 as [d [d_eq d_nocode]]. rewrite d_eq in HeqH. simplify_some. done.
        * eapply wf_stack_cons_right; eauto.
          -- rewrite eq_s1'. simpl.
             unfold points_to_comp_code'. rewrite setmE. 
             remember (@eq_op (Ord.eqType _) v1 w) as cond. unfold mt, concrete_int_32_mt, word_size in Heqcond.
             destruct cond; try exact PTS_CODE1.
             assert (eq_w: v1 = w) by eq_op_to_eq. subst v1. simpl.
             unfold points_to_comp_code' in PTS_CODE1.
             oapp_False.
             rewrite (same_color a); try left; auto. destruct PTS_CODE1 as [eqC disj]. split; (try rewrite <- v_color); auto.
             left. split; auto. simpl in SIDE.
             assert (cond_eq: C \in domm ip = false).
             { assert (~ C \in domm ip). intro. 
               { eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
                 inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. }
               remember (C \in domm ip) as cond. destruct cond; auto. destruct H. done. }
             unfold side_of in *.
             rewrite cond_eq. done.
          -- simpl.
             unfold points_to_comp_code. rewrite setmE. 
             remember (@eq_op (Ord.eqType _) v3 w) as cond. unfold mt, concrete_int_32_mt, word_size in Heqcond.
             destruct cond; try exact PTS_CODE3.
             assert (eq_w: v3 = w) by eq_op_to_eq. subst w.
             exfalso. unfold points_to_comp_code in PTS_CODE3.
             oapp_False.
             destruct PTS_CODE3 as [color_a code_a].
             destruct no_code_w_s3 as [d [d_eq d_nocode]]. rewrite d_eq in HeqH. simplify_some. done. 
      + admit. (* domains remain unchanged *)
      + admit. (* domains remain unchanged *)
      + unfold alloc_empty in *. subst. simpl in *. rewrite setmE.
        remember (@eq_op (Ord.eqType _) (word_of_nat alloc_label) w) as cond.
        destruct cond; try (eapply (alloc_mem_s1)). exfalso.
        rewrite eq_sym in Heqcond. convert_eq_op.
        unfold updm in eq_m1. rewrite alloc_mem_s1 in eq_m1. simpl in eq_m1. inversion eq_m1.
      + intros d w' deq dcode. subst. simpl in deq. rewrite setmE in deq.
        remember (@eq_op (Ord.eqType _) d w) as cond. simpl in *. rewrite <- Heqcond in deq.
        destruct cond; try (simplify_some; contradiction).
        (pose proof (bnz_s1 d w' deq dcode)). simpl in *. unfold_bind. simpl.
        goal_match_bind_step; try done; try destruct H as [? [eq1 ?]].
        -- remember (@eq_op (Ord.eqType _) (d + swcast i0)%w w) as cond1; destruct cond1;
             eexists; simpl in *; rewrite setmE; rewrite <- Heqcond1.
           ++ destruct no_code_w_s1 as [? [eq2 ?]]. convert_eq_op. rewrite eq2 in eq1. simplify_some. contradiction.
           ++ split; [exact eq1 | done].
        -- destruct H as [[? [eq1 ?]] | eq_alloc]; try (right; done).
            left; remember (@eq_op (Ord.eqType _) (swcast i0)%w w) as cond1; destruct cond1;
             eexists; simpl in *; rewrite setmE; rewrite <- Heqcond1.
          ++ destruct no_code_w_s1 as [? [eq2 ?]]. convert_eq_op. rewrite eq2 in eq1. simplify_some. contradiction.
          ++ split; [exact eq1 | done].
      + unfold end_condition in *. intros w0 v0 v0_eq v0_code.
        rewrite eq_s1' in v0_eq. simpl in v0_eq. rewrite setmE in v0_eq.
        remember (@eq_op (Ord.eqType _) w0 w) as cond. simpl in Heqcond. rewrite <- Heqcond in v0_eq. destruct cond.
        * simplify_some. contradiction.
        * destruct (end_s1 w0 v0 v0_eq v0_code); [left | right]; auto. destruct H as [v1 [v1_eq v1_code]].
          exists v1. rewrite eq_s1'. rewrite setmE.
          remember (@eq_op (Ord.eqType _) (addw w0 onew) w) as cond. destruct cond; try (split; done).
          exfalso. assert ((addw w0 onew) = w) by eq_op_to_eq. subst w.
          destruct no_code_w_s1 as [? [eq no_code]]. rewrite eq in v1_eq. simplify_some. done.
      + intros w' d deq. subst. simpl in deq.
        rewrite setmE in deq. unfold_match' deq; try convert_eq_op; try simplify_some.
        simpl in v_relevant. left. eapply ((fst (Extra.In_in _ _)) v_relevant).
        eapply col_mem1; eauto.
      + admit. (* domains remain unchanged *)
      + admit. (* domains remain unchanged *)
      + unfold alloc_empty in *. subst. simpl in *. rewrite setmE.
        remember (@eq_op (Ord.eqType _) (word_of_nat alloc_label) w) as cond.
        destruct cond; try (eapply (alloc_mem_s3)). exfalso.
        rewrite eq_sym in Heqcond. convert_eq_op.
        unfold updm in eq_m1. rewrite alloc_mem_s1 in eq_m1. simpl in eq_m1. inversion eq_m1.
      + intros d w' deq dcode. subst. simpl in deq. rewrite setmE in deq.
        remember (@eq_op (Ord.eqType _) d w) as cond. simpl in *. rewrite <- Heqcond in deq.
        destruct cond; try (simplify_some; contradiction).
        (pose proof (bnz_s3 d w' deq dcode)). simpl in *. unfold_bind. simpl.
        goal_match_bind_step; try done; try destruct H as [? [eq1 ?]].
        -- remember (@eq_op (Ord.eqType _) (d + swcast i0)%w w) as cond1; destruct cond1;
             eexists; simpl in *; rewrite setmE; rewrite <- Heqcond1.
           ++ destruct no_code_w_s3 as [? [eq2 ?]]. convert_eq_op. rewrite eq2 in eq1. simplify_some. contradiction.
           ++ split; [exact eq1 | done].
        -- destruct H as [[? [eq1 ?]] | eq_alloc]; try (right; done).
           left; remember (@eq_op (Ord.eqType _) (swcast i0)%w w) as cond1; destruct cond1;
             eexists; simpl in *; rewrite setmE; rewrite <- Heqcond1.
          ++ destruct no_code_w_s3 as [? [eq2 ?]]. convert_eq_op. rewrite eq2 in eq1. simplify_some. contradiction.
          ++ split; [exact eq1 | done].
      + unfold end_condition in *. intros w0 v0 v0_eq v0_code.
        rewrite eq_s3' in v0_eq. simpl in v0_eq. rewrite setmE in v0_eq.
        remember (@eq_op (Ord.eqType _) w0 w) as cond. simpl in Heqcond. rewrite <- Heqcond in v0_eq. destruct cond.
        * simplify_some. contradiction.
        * destruct (end_s3 w0 v0 v0_eq v0_code); [left | right]; auto. destruct H as [v1 [v1_eq v1_code]].
          exists v1. rewrite eq_s3'. rewrite setmE.
          remember (@eq_op (Ord.eqType _) (addw w0 onew) w) as cond. destruct cond; try (split; done).
          exfalso. assert ((addw w0 onew) = w) by eq_op_to_eq. subst w.
          destruct no_code_w_s3 as [? [eq no_code]]. rewrite eq in v1_eq. simplify_some. done.
      + intros w' d deq. subst. simpl in deq.
        rewrite setmE in deq. unfold_match' deq; try convert_eq_op; try simplify_some.
        rewrite v_color in v_relevant. simpl in v_relevant. left. eapply ((fst (Extra.In_in _ _)) v_relevant).
        eapply col_mem3; eauto.
      + unfold combined_codes. intros w' d t off comp relevant_comp offset v'_code v'_color.
        remember (addw w' (as_word off)) as w''. subst s1' s3'. simpl.
        repeat rewrite setmE.
        remember (@eq_op (Ord.eqType _) w'' w) as cond1.
        remember (@eq_op (Ord.eqType _) w' w) as cond2. unfold mt, concrete_int_32_mt, word_size in Heqcond1, Heqcond2.
        rewrite <- Heqcond1, <- Heqcond2.
        destruct v as [? vt], v' as [? vt']. inversion v_match. subst vt'.
        pose proof (code_left w' d t off comp relevant_comp offset v'_code v'_color) as [impll implr].
        destruct cond1; destruct cond2; convert_eq_op; simpl; split; intro eq; try simplify_some; subst.
        all: try contradiction.
        * destruct (impll eq) as [? [? eq1]]. destruct no_code_w_s3 as [? [eq2 ?]]. rewrite eq1 in eq2. simplify_some. contradiction.
        * destruct (implr eq) as [? [? eq1]]. destruct no_code_w_s1 as [? [eq2 ?]]. rewrite eq1 in eq2. simplify_some. contradiction.
        * destruct (impll eq) as [d' [decode_d' d'_eq]]. exists d'. split; auto.
          inversion decode_d'; subst.
          -- econstructor; trivial.
          -- eapply decode_match_alloc_JAL; trivial.
          -- eapply decode_match_JAL. exact H. exact H1.
             rewrite setmE.
             destruct (@eq_op (Ord.eqType _) (swcast imm) w) eqn:cond1; repeat simplify_some.
             { exfalso. pose proof (esym cond1). convert_eq_op. destruct no_code_w_s1 as [? [eq1 ?]].
               rewrite H2 in eq1. simplify_some. tauto. }
             { exact H2. }
             rewrite setmE.
             destruct (@eq_op (Ord.eqType _) (swcast imm') w) eqn:cond1; repeat simplify_some.
             { exfalso. pose proof (esym cond1). convert_eq_op. destruct no_code_w_s3 as [? [eq1 ?]].
               rewrite H3 in eq1. simplify_some. rewrite H5 in H4. tauto. }
             { exact H3. }
             all: trivial.
        * destruct (implr eq) as [d' [decode_d' d'_eq]]. exists d'. split; auto.
          inversion decode_d'; subst.
          -- econstructor; trivial.
          -- eapply decode_match_alloc_JAL; trivial.
          -- eapply decode_match_JAL. exact H. exact H1.
             rewrite setmE.
             destruct (@eq_op (Ord.eqType _) (swcast imm) w) eqn:cond1; repeat simplify_some.
             { exfalso. pose proof (esym cond1). convert_eq_op. destruct no_code_w_s1 as [? [eq1 ?]].
               rewrite H2 in eq1. simplify_some. tauto. }
             { exact H2. }
             rewrite setmE.
             destruct (@eq_op (Ord.eqType _) (swcast imm') w) eqn:cond1; repeat simplify_some.
             { exfalso. pose proof (esym cond1). convert_eq_op. destruct no_code_w_s3 as [? [eq1 ?]].
               rewrite H3 in eq1. simplify_some. rewrite H5 in H4. tauto. }
             { exact H3. }
             all: trivial.
      +  unfold combined_codes. intros w' d t off comp relevant_comp offset v'_code v'_color.
        remember (addw w' (as_word off)) as w''. subst s1' s3'. simpl.
        repeat rewrite setmE.
        remember (@eq_op (Ord.eqType _) w'' w) as cond. unfold mt, concrete_int_32_mt, word_size in Heqcond.
        rewrite <- Heqcond.
        destruct v as [? vt], v' as [? vt']. inversion v_match. subst vt'.
        pose proof (code_right w' d t off comp relevant_comp offset v'_code v'_color) as [impll implr].
        destruct cond; convert_eq_op; simpl; split; intro eq; try simplify_some; subst.
        all: try contradiction.
        destruct (impll eq) as [? [? eq1]]. destruct no_code_w_s3 as [? [eq2 ?]]. rewrite eq1 in eq2. simplify_some. contradiction.
        * destruct (impll eq) as [d' [decode_d' d'_eq]]. exists d'. split; auto.
          inversion decode_d'; subst.
          -- econstructor; trivial.
          -- eapply decode_match_alloc_JAL; trivial.
          -- eapply decode_match_JAL. exact H. exact H1.
             exact H2.
             rewrite setmE.
             destruct (@eq_op (Ord.eqType _) (swcast imm') w) eqn:cond1; repeat simplify_some.
             { exfalso. pose proof (esym cond1). convert_eq_op. destruct no_code_w_s3 as [? [eq1 ?]].
               rewrite H3 in eq1. simplify_some. rewrite H5 in H4. tauto. }
             { exact H3. }
             all: trivial.
        * destruct (implr eq) as [d' [decode_d' d'_eq]]. exists d'. split; auto.
          inversion decode_d'; subst.
          -- econstructor; trivial.
          -- eapply decode_match_alloc_JAL; trivial.
          -- eapply decode_match_JAL. exact H. exact H1.
             exact H2.
             rewrite setmE.
             destruct (@eq_op (Ord.eqType _) (swcast imm') w) eqn:cond1; repeat simplify_some.
             { exfalso. pose proof (esym cond1). convert_eq_op. destruct no_code_w_s3 as [? [eq1 ?]].
               rewrite H3 in eq1. simplify_some. rewrite H5 in H4. tauto. }
             { exact H3. }
             all: trivial.
  Admitted.

  Lemma preserves_equiv_left_reg_write :
    forall s1 s2 s3 M s1' s3' r v v'  r1' r3',
      strong_equiv Left M s1 s3
      /\ weak_equiv Right M s2 s3
      /\ common_equiv M s1 s2 s3 ->
      data_match Left (color_of s1) M v v' ->
      address_correctness (vala v) (taga v) (mem s1) ->
      address_correctness (vala v') (taga v') (mem s3) ->
      updm (regs s1) r v = Some r1' ->
      updm (regs s3) r v' = Some r3' ->
      s1' = State _ _ (mem s1) r1' (pc s1) tt (comp_num s1) ->
      s3' = State _ _ (mem s3) r3' (pc s3) tt (comp_num s3) ->
      strong_equiv Left M s1' s3'
      /\ weak_equiv Right M s2 s3'
      /\ common_equiv M s1' s2 s3'.
  Proof.
    intros s1 s2 s3 M s1' s3' r v v' r1' r3' equiv v_match
      correct_v correct_v' eq_r1 eq_r3 eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    destruct common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 col_mem1]]]]]
                          [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 col_mem2]]]]]
                          [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 col_mem3]]]]] code_left code_right].
    pose proof (updm_set eq_r1). pose proof (updm_set eq_r3). subst r1' r3'. 
    split; [|split].
    - destruct strong as [? ? ? wf_m num_eq pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
      econstructor; destruct s, s', pc0, pc1; try (rewrite eq_s1' eq_s3'; simpl; auto; done); try (subst; simpl; trivial; done); try congruence.
      + destruct pc_s1_s3 as [? ? ? eq_none|? ? ? ? eq_comp eq_off pc_s1_s3].
        * eapply same_pc_alloc; try rewrite eq_s1'; try rewrite eq_s3'; auto.
        * eapply same_pc_normal; eauto. subst. simpl. exact eq_comp.
          subst. simpl. destruct s, pc0. exact eq_off.
          rewrite eq_s1' eq_s3'. simpl. done.
      + subst. intros d w' deq. simpl in *. auto. destruct d as [vd vt].
        rewrite setmE in deq. remember (@eq_op (Ord.eqType _) w' r) as cond.
        destruct vt; simpl; auto; destruct cond;
          try eapply (s_reg_cor _ w' deq).
          try (convert_eq_op; try simplify_some; eapply correct_v).
          convert_eq_op. simplify_some. simpl in correct_v. done.
      + subst. intros d w' deq. simpl in *. auto. destruct d as [vd vt].
        rewrite setmE in deq. remember (@eq_op (Ord.eqType _) w' r) as cond.
        destruct vt; simpl; auto; destruct cond;
          try eapply (s'_reg_cor _ w' deq);
          try (convert_eq_op; try simplify_some; eapply correct_v').
      + unfold registers_match in *. rewrite eq_s1' eq_s3'. simpl. 
        intros. rewrite setmE. rewrite setmE.
        remember (@eq_op (Ord.eqType _) w r) as cond. destruct cond.
        * split; intro eq; simplify_some; eauto.
        * apply reg_match; auto.
    - destruct weak as [? ? s3 wf_m num_eq color_eq side_s' s_mem_cor s'_mem_cor entry_off mem_match].
      econstructor; try (rewrite eq_s3'; simpl; auto; done); try congruence.
      destruct s, s3, pc0, pc1. subst. simpl. auto. trivial.
    - eapply common_equiv_def with (n := n) (c := c0); 
        try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; try done.
      + subst. unfold register_domm. simpl. rewrite domm_set. 
        unfold register_domm, reg_field_size in *. simpl in *. unfold updm in eq_r1. unfold_match' eq_r1.
        clear -Heqa reg_domm1. admit.
      + subst. unfold register_domm. simpl. rewrite domm_set. 
        unfold register_domm, reg_field_size in *. simpl in *. unfold updm in eq_r3. unfold_match' eq_r3.
        clear -Heqa reg_domm3. admit.
  Admitted.

  
  Lemma preserves_equiv_left_alloc_fun:
    forall s1 s2 s3 M s1' s3',
      strong_equiv Left M s1 s3
      /\ weak_equiv Right M s2 s3
      /\ common_equiv M s1 s2 s3 ->
      alloc_fun s1 = Some s1' ->
      alloc_fun s3 = Some s3' ->
      strong_equiv Left M s1' s3'
      /\ weak_equiv Right M s2 s3'
      /\ common_equiv M s1' s2 s3'.
  Proof.
    intros s1 s2 s3 M s1' s3' equiv eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    unfold alloc_fun in *.
    repeat (unfold_all || unfold_match).
    unfold is_jump, is_other in *. 
    repeat (unfold_all || unfold_match).
    destruct a as [v tmp]. destruct a2 as [v' tmp']. simpl in *. subst tmp tmp'.
    rename n into n'.
    inversion common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 col_mem1]]]]]
                          [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 col_mem2]]]]]
                          [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 col_mem3]]]]] code_left code_right].
    subst m s0 s4 s5.
    assert (n1 = n').
    { destruct strong as [? ? ? wf_m ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
      destruct (reg_match (as_word (ssrint.Posz 17)) v'@Other) as [_ impl].
      destruct (impl (esym Heqa5)) as [? [dmatch eq1]]. simpl in *. rewrite eq1 in Heqa1.
      simplify_some. destruct x. 
      destruct dmatch. simpl in *. subst. rewrite <- Heqa8 in Heqa12.
      rename Heqa12 into eq. clear -eq.
      pose proof (congr1 ssrint.absz eq) as eq'.
      repeat rewrite ssrint.absz_nat in eq'. done. } subst n1.
    split; [|split].
    - destruct strong as [? ? ? wf_m num_eq pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
      econstructor; try (destruct s, s', pc0, pc1; try (rewrite eq_s1' eq_s3'; simpl; auto; done); try congruence; simpl; done).
      + intros v1 v2 v3 v0 comp off inclusion side_c0 off_eq.
        destruct (wf_m v1 v2 v3 v0 comp off inclusion side_c0 off_eq) as [? [? ?]].
        unfold points_to_comp_code, points_to_comp_code' in *. simpl.
        do 2 oapp_False. 
        repeat rewrite unionmE. simpl in *. rewrite <- HeqH0. rewrite <- HeqH2. simpl. done.
      + pose proof ((fst (reg_match _ v@InternalJump)) (esym Heqa)) as [d' [d'match d'eq]].
        simpl in *. rewrite <- Heqa3 in d'eq. simplify_some. destruct d' as [? taga1].
        destruct d'match as [? ?]. subst taga1. oapp_False.
        pose proof (s_reg_cor _ _ (esym Heqa3)). destruct H as [? [eq ?]].
        eapply same_pc_normal; simpl; try done; eauto.
        rewrite unionmE. rewrite eq. simpl. trivial.
        destruct s, s', pc0, pc1. rewrite HeqH. simpl. trivial.
      + intros d w rel d_eq. simpl. destruct d as [vd td]. destruct td.
        destruct vtag; simpl; auto.
        all: rewrite unionmE; rewrite unionmE in d_eq; simpl in *.
        all: remember (mem s w) as cond; simpl in *.
        all: rewrite <- Heqcond in d_eq; destruct cond; simpl in *.
        all: try (pose proof (s_mem_cor a w ); simplify_some; simpl in *;
                  pose proof (H rel (esym Heqcond)) as [d' [d'eq d'cond]];
                  rewrite d'eq; simpl; eauto).
        all: exfalso; clear - d_eq.
        all: unfold mkfmap, mkseq, foldr, map in *.
        all: remember (iota 0 n') as l; clear Heql. 
        all: induction l; simpl in *; try (inversion d_eq; done).
        all: rewrite setmE in d_eq; unfold_match; simpl in *; auto.
      + intros d w rel d_eq. simpl. destruct d as [vd td]. destruct td.
        destruct vtag; simpl; auto.
        all: rewrite unionmE; rewrite unionmE in d_eq; simpl in *.
        all: remember (mem s' w) as cond; simpl in *.
        all: rewrite <- Heqcond in d_eq; destruct cond; simpl in *.
        all: try (pose proof (s'_mem_cor a w ); simplify_some; simpl in *;
                  pose proof (H rel (esym Heqcond)) as [d' [d'eq d'cond]];
                  rewrite d'eq; simpl; eauto).
        all: exfalso; clear - d_eq.
        all: unfold mkfmap, mkseq, foldr, map in *.
        all: remember (iota 0 n') as l; clear Heql. 
        all: induction l; simpl in *; try (inversion d_eq; done).
        all: rewrite setmE in d_eq; unfold_match; simpl in *; auto.
      + subst. simpl. intros col w' w'' d d' e rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq.
        rewrite unionmE in eqw'. rewrite unionmE in eqw''.
        unfold_match' eqw'; unfold_match' eqw''.
        * eapply entry_off; eauto.
        * assert (~ (is_code (taga d'))) by admit. tauto.
        * assert (~ (is_code (taga d))) by admit. tauto.
        * assert (~ (is_code (taga d'))) by admit. tauto.
      + intros d w d_eq. simpl in *. destruct d as [vd td].
        destruct td; simpl; auto.
        all: rewrite unionmE; rewrite setmE in d_eq; simpl in *.
        all: remember (@eq_op (Ord.eqType _) w (as_word (ssrint.Posz 16))) as cond; simpl in *.
        all: destruct cond; simpl in *.
        all: try simplify_some.
        all: pose proof (s_reg_cor _ w d_eq) as H; simpl in H; destruct H as [d' [? ?]].
        all: rewrite H; simpl; eauto.
      + intros d w d_eq. simpl in *. destruct d as [vd td].
        destruct td; simpl; auto.
        all: rewrite unionmE; rewrite setmE in d_eq; simpl in *.
        all: remember (@eq_op (Ord.eqType _) w (as_word (ssrint.Posz 16))) as cond; simpl in *.
        all: destruct cond; simpl in *.
        all: try simplify_some.
        all: pose proof (s'_reg_cor _ w d_eq) as H; simpl in H; destruct H as [d' [? ?]].
        all: rewrite H; simpl; eauto.
      + intros w d no_code rel. simpl. repeat rewrite unionmE.
        split.
        * remember (mem s' w) as cond. simpl in *. rewrite <- Heqcond. destruct cond; simpl.
          -- intro. simplify_some.
             pose proof (mem_match w d) as [impl _]; auto; simpl.
             destruct (impl (esym Heqcond)) as [d' [d'match d'eq]].
             rewrite d'eq. simpl. exists d'. done.
          -- intro. exists d.
             assert (d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s') false)) by admit.
             subst d. split; simpl; try done. simpl in *.
             remember (mem s w) as cond. destruct cond.
             { assert (w_prefix: (andw w (@component_memory_prefix mt (ssrint.Posz (2 ^ comp_num s' - 1)) (comp_num s')) ==
                                    @component_memory_prefix mt (ssrint.Posz (1 + color_of s')) (comp_num s'))).
               { clear -H. admit. }
               destruct (is_code (taga a)) eqn:code.
               { clear -code_pref_cond_s1 Heqcond0 code w_prefix. exfalso. admit. }
               pose proof (mem_match w a) as [_ impl]; auto; simpl; try (rewrite code; done).
               { clear -w_prefix rel code Heqcond0 mem_pref_cond_s1.
                 assert (color (taga a) = color_of s') as eq by admit. rewrite eq. done. }
               destruct (impl (esym Heqcond0)) as [d' [d'match d'eq]]. simpl in *.
               rewrite <- Heqcond in d'eq. inversion d'eq. }
             simpl in *. rewrite <- Heqcond0. simpl.
             assert (eq: comp_num s = comp_num s') by done. rewrite eq.
             rewrite tag_pc1. rewrite tag_pc3 in H. clear -H mem_pref_cond_s1. admit.
        * remember (mem s w) as cond. simpl in *. rewrite <- Heqcond. destruct cond; simpl.
          -- intro. simplify_some.
             pose proof (mem_match w d) as [_ impl]; auto; simpl.
             destruct (impl (esym Heqcond)) as [d' [d'match d'eq]].
             rewrite d'eq. simpl. exists d'. done.
          -- intro. exists d.
             assert (d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s) false)) by admit.
             subst d. split; simpl; try done. simpl in *.
             remember (mem s' w) as cond. destruct cond.
             { assert (w_prefix: (andw w (@component_memory_prefix mt (ssrint.Posz (2 ^ comp_num s - 1)) (comp_num s)) ==
                                    @component_memory_prefix mt (ssrint.Posz (1 + color_of s)) (comp_num s))).
               { clear -H. admit. }
               destruct (is_code (taga a)) eqn:code.
               { clear -code_pref_cond_s3 Heqcond0 code w_prefix. exfalso. admit. }
               pose proof (mem_match w a) as [impl _]; auto; simpl; try (rewrite code; done).
               { clear -w_prefix rel code Heqcond0 mem_pref_cond_s3.
                 assert (color (taga a) = color_of s) as eq by admit. rewrite eq. done. }
               destruct (impl (esym Heqcond0)) as [d' [d'match d'eq]]. simpl in *.
               rewrite <- Heqcond in d'eq. inversion d'eq. }
             simpl in *. rewrite <- Heqcond0. simpl.
             assert (eq: comp_num s = comp_num s') by done. rewrite <- eq.
             rewrite tag_pc3. rewrite tag_pc1 in H. clear -H mem_pref_cond_s3. admit.
      + intros w d. simpl. repeat rewrite setmE.
        remember (@eq_op (Ord.eqType _) w (as_word (ssrint.Posz 16))) as cond.
        assert (p1 = p2).
        { assert (eq: comp_num s = comp_num s') by done. rewrite eq in Heqa13.
          rewrite tag_pc1 in Heqa13. rewrite tag_pc3 in Heqa10.
          clear -Heqa10 Heqa13. admit. }
        subst p2.
        simpl in *. rewrite <- Heqcond. destruct cond; simpl.
        split; intro; simplify_some; eexists; split; eauto.
        all: destruct s, pc0; try eapply reg_match.
        all: simpl in *; split; auto.
    - destruct weak as [? ? s3 wf_m num_eq color_eq side_s' s_mem_cor s'_mem_cor entry_off mem_match].
      econstructor; try (rewrite eq_s3'; simpl; auto; done); try congruence; simpl; try done.
      + intros v1 v2 v3 v0 comp off inclusion side_c0 off_eq.
        destruct (wf_m v1 v2 v3 v0 comp off inclusion side_c0 off_eq) as [? [? ?]].
        unfold points_to_comp_code, points_to_comp_code' in *. simpl.
        do 2 oapp_False. 
        repeat rewrite unionmE. simpl in *. rewrite <- HeqH0. rewrite <- HeqH2. simpl. done.
      + destruct s, s3, pc0, pc1. simpl. trivial.
      + intros d w rel d_eq. simpl. destruct d as [vd td]. destruct td.
        destruct vtag; simpl; auto.
        all: rewrite unionmE; rewrite unionmE in d_eq; simpl in *.
        all: remember (mem s3 w) as cond; simpl in *.
        all: rewrite <- Heqcond in d_eq; destruct cond; simpl in *.
        all: try (pose proof (s'_mem_cor a w ); simplify_some; simpl in *;
                  pose proof (H rel (esym Heqcond)) as [d' [d'eq d'cond]];
                  rewrite d'eq; simpl; eauto).
        all: exfalso; clear - d_eq.
        all: unfold mkfmap, mkseq, foldr, map in *.
        all: remember (iota 0 n') as l; clear Heql. 
        all: induction l; simpl in *; try (inversion d_eq; done).
        all: rewrite setmE in d_eq; unfold_match; simpl in *; auto.
      + subst. simpl. intros col w' w'' d d' e rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq.
        rewrite unionmE in eqw''.
        unfold_match' eqw''.
        * eapply entry_off; eauto.
        * assert (~ (is_code (taga d'))) by admit. tauto.
      + intros w d no_code rel. simpl. repeat rewrite unionmE.
        split.
        * remember (mem s3 w) as cond. simpl in *. rewrite <- Heqcond. destruct cond; simpl.
          -- intro. simplify_some.
             pose proof (mem_match w d) as [impl _]; auto; simpl.
          -- intro. exfalso.
             assert (w_prefix: (andw w (@component_memory_prefix mt (ssrint.Posz (2 ^ comp_num s3 - 1)) (comp_num s3)) ==
                                  @component_memory_prefix mt (ssrint.Posz (1 + color_of s3)) (comp_num s3))).
             { clear -H. admit. }
             assert (d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
             subst d. simpl in rel.
             unfold side_of in side_s'. unfold_match' side_s'.
             eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
             inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto.
             clear -color_eq Heqa0. rewrite <- color_eq. rewrite <- Heqa0. trivial.
        * remember (mem s w) as cond. simpl in *. rewrite <- Heqcond. destruct cond; simpl; intro eq; try (inversion eq; done).
          simplify_some.
          pose proof (mem_match w d) as [_ impl]; auto; simpl. destruct (impl (esym Heqcond)) as [? [? ?]]. rewrite H0.
          simpl. eauto.
    - eapply common_equiv_def with (n := n) (c := c0); 
        try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; simpl; try done.
      + simpl. clear strong common weak code_left code_right tag_pc1 tag_pc2 tag_pc3.
        simpl in *. 
        induction wfst; intros.
        * eapply wf_stack_empty; eauto.
        * eapply wf_stack_cons_left; eauto.
          -- unfold points_to_comp_code' in *. rewrite unionmE.
             oapp_False. simpl. done.
          -- unfold points_to_comp_code in *. rewrite unionmE.
             oapp_False. simpl. done.
        * eapply wf_stack_cons_right; eauto.
          -- unfold points_to_comp_code' in *. rewrite unionmE.
             oapp_False. simpl. done.
          -- unfold points_to_comp_code in *. rewrite unionmE.
             oapp_False. simpl. done.
      + unfold register_domm. simpl. rewrite domm_set. 
        unfold register_domm, reg_field_size in *. simpl in *. clear -reg_domm1. admit.
      + unfold register_domm. simpl. rewrite domm_set. 
        unfold register_domm, reg_field_size in *. simpl in *. clear -reg_domm3. admit.
      + split; [|split; [|split; [|split; [|split]]]];
          unfold memory_prefix_condition, code_prefix_condition, alloc_empty, BNZ_correctness, end_condition in *;
          simpl; repeat rewrite unionmE.
        * admit.
        * admit.
        * rewrite alloc_mem_s1. simpl. admit.
        * intros w d deq dcode. goal_match_bind_step.
          rewrite unionmE in deq. unfold_match' deq.
          all: auto.
          { (pose proof (bnz_s1 w d deq dcode) as cor; unfold decode_instr, ops, concrete_int_32_ops in cor).
            simpl in *; rewrite <- Heqa0 in cor. destruct i; auto; simpl; rewrite unionmE.
            + destruct cor as [? [eq ?]]. rewrite eq. simpl. eauto.
            + destruct cor as [[? [eq ?] ]| ]. rewrite eq. simpl. eauto.
              rewrite H. right. done. }
          { assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)) by admit.
            rewrite eq in Heqa0. exfalso. clear -Heqa0. simpl in *. unfold_all. rewrite wunpackS in Heqa.
            unfold hnth in *. simpl in *. lazy in Heqa. inv Heqa. }
        * intros w d deq dcode. rewrite unionmE in deq.
          remember (mem s1 (w)) as cond. simpl in *. rewrite <- Heqcond in deq. destruct cond.
          { simpl in deq. simplify_some. destruct (end_s1 _ _ (esym Heqcond)); auto.
            right. destruct H as [d' [d'eq ?]]. exists d'.
            rewrite unionmE. rewrite d'eq. simpl. done. }
          { assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)) by admit.
            subst d. simpl in dcode. inversion dcode. }
        * intros w d deq. rewrite unionmE in deq. unfold_match' deq.
          -- eapply col_mem1; eauto.
          -- admit.
      + split; [|split; [|split; [|split; [|split]]]];
          unfold memory_prefix_condition, code_prefix_condition, alloc_empty, BNZ_correctness, end_condition in *;
          simpl; repeat rewrite unionmE.
        * admit.
        * admit.
        * rewrite alloc_mem_s3. simpl. admit.
        * intros w d deq dcode. goal_match_bind_step.
          rewrite unionmE in deq. unfold_match' deq.
          all: auto.
          { (pose proof (bnz_s3 w d deq dcode) as cor; unfold decode_instr, ops, concrete_int_32_ops in cor).
            simpl in *; rewrite <- Heqa0 in cor. destruct i; auto; simpl; rewrite unionmE.
            + destruct cor as [? [eq ?]]. rewrite eq. simpl. eauto.
            + destruct cor as [[? [eq ?] ]| ]. rewrite eq. simpl. eauto.
              rewrite H. right. done. }
          { assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
            rewrite eq in Heqa0. exfalso. clear -Heqa0. simpl in *. unfold_all. rewrite wunpackS in Heqa.
            lazy in Heqa. inv Heqa. }
        * intros w d deq dcode. rewrite unionmE in deq.
          remember (mem s3 (w)) as cond. simpl in *. rewrite <- Heqcond in deq. destruct cond.
          { simpl in deq. simplify_some. destruct (end_s3 _ _ (esym Heqcond)); auto.
            right. destruct H as [d' [d'eq ?]]. exists d'.
            rewrite unionmE. rewrite d'eq. simpl. done. }
          { assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
            subst d. simpl in dcode. inversion dcode. }
        * intros w d deq. rewrite unionmE in deq. unfold_match' deq.
          -- eapply col_mem3; eauto.
          -- admit.
      + unfold combined_codes in *. simpl in *.
        intros w d t off col rel eq_off dcode dcol. repeat rewrite unionmE.
        remember (mem s3 (addw w (as_word off))) as cond1.
        remember (mem s1 w) as cond2.
        simpl in *. rewrite <- Heqcond1. rewrite <- Heqcond2.
        destruct cond1; destruct cond2; split; simpl; intro Heq; try simplify_some; subst; simpl.
        -- rewrite Heqcond1. destruct ((fst (code_left w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond2)) as [x [xmatch xeq]].
           exists x. split; auto.
           inversion xmatch; subst.
           ++ econstructor; eauto.
           ++ eapply decode_match_alloc_JAL; eauto.
           ++ eapply decode_match_JAL. exact H. exact H0.
              rewrite unionmE. rewrite H1. simpl. eauto.
              rewrite unionmE. rewrite H2. simpl. eauto.
              all: trivial.
        -- rewrite Heqcond2. destruct ((snd (code_left w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond1)) as [x [xmatch xeq]].
           exists x. split; auto.
           inversion xmatch; subst.
           ++ econstructor; eauto.
           ++ eapply decode_match_alloc_JAL; eauto.
           ++ eapply decode_match_JAL. exact H. exact H0.
              rewrite unionmE. rewrite H1. simpl. eauto.
              rewrite unionmE. rewrite H2. simpl. eauto.
              all: trivial.
        -- assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)) by admit.
           inv eq. exfalso. discriminate.
        -- destruct ((snd (code_left w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond1)) as [? [? eq1]].
           exfalso. congruence.
        -- destruct ((fst (code_left w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond2)) as [? [? eq1]].
           exfalso. congruence.
        -- assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
           inv eq. exfalso. discriminate.
        -- assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)) by admit.
           inv eq. exfalso. discriminate.
        -- assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
           inv eq. exfalso. discriminate.
      + unfold combined_codes in *. simpl in *.
        intros w d t off col rel eq_off dcode dcol. repeat rewrite unionmE.
        remember (mem s3 (addw w (as_word off))) as cond1.
        remember (mem s2 w) as cond2.
        simpl in *. rewrite <- Heqcond1. rewrite <- Heqcond2.
        destruct cond1; destruct cond2; split; simpl; intro Heq; try simplify_some; subst; simpl; try (inversion Heq; done).
        -- rewrite Heqcond1. destruct ((fst (code_right w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond2)) as [x [xmatch xeq]].
           exists x. split; auto.
           inversion xmatch; subst.
           ++ econstructor; eauto.
           ++ eapply decode_match_alloc_JAL; eauto.
           ++ eapply decode_match_JAL. exact H. exact H0.
              exact H1.
              rewrite unionmE. rewrite H2. simpl. eauto.
              all: trivial.
        -- rewrite Heqcond2. destruct ((snd (code_right w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond1)) as [x [xmatch xeq]].
           exists x. split; auto.
           inversion xmatch; subst.
           ++ econstructor; eauto.
           ++ eapply decode_match_alloc_JAL; eauto.
           ++ eapply decode_match_JAL. exact H. exact H0.
              exact H1.
              rewrite unionmE. rewrite H2. simpl. eauto.
              all: trivial.
        -- destruct ((snd (code_right w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond1)) as [? [? eq1]].
           exfalso. congruence.
        -- destruct ((fst (code_right w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond2)) as [? [? eq1]].
           exfalso. congruence.
        -- assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
           inv eq. exfalso. discriminate.
        -- assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
           inv eq. exfalso. discriminate.
  Admitted.
  
  (*** Diagrams ***)
  
  
  Lemma initial_memory_domm: forall b,
      domm (@initial_memory mt b) = fset (map word_of_nat (List.seq 0 (size (@initial_memory mt b)))).
  Proof.
    intros.
  Admitted.
  
  Lemma encode_code_domm: forall cd pc,
      domm (encode_code cd pc) = fset (map word_of_nat (List.seq pc (size cd))).
  Proof.
    intros.
  Admitted.
  
  
  Lemma match_initial_states:
  forall s1, Smallstep.initial_state sem s1 ->
  forall s2, Smallstep.initial_state sem' s2 ->
  exists s3 M, Smallstep.initial_state sem'' s3 /\ match_states M s1 s2 s3.
  Proof.
    intros s1 init1 s2 init2.
    unfold Smallstep.initial_state, sem, sem' in init1, init2. simpl in init1. unfold initial_state1, initial_state2 in *.
    remember (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')) as s3.
    rename Heqs3 into init3.
    exists s3. exists [].
    split; try (simpl; unfold initial_state3; done).
    remember (prog_main p) as main. destruct main; [eapply match_states_left | eapply match_states_right]; try (eapply common_equiv_def || econstructor); simpl.
    - unfold initial_state in init1. simpl in init1. destruct s1. inv init1. simpl. done.
    - unfold initial_state in init2. simpl in init2. destruct s2. inv init2. simpl. done.
    - unfold initial_state in init3. simpl in init3. destruct s3. inv init3. simpl. done.
    - rewrite init3. simpl. econstructor.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - unfold combined_codes. intros. admit.
    - unfold combined_codes. intros. admit.
    - admit.
    - unfold well_formed_metadata. intros. inv H.
    - subst. unfold initial_state. simpl. rewrite Hifacep Hifacec. trivial.
    - assert (color_eq: color_of s1 = 0). subst. unfold initial_state, color_of. simpl. trivial.
  Admitted.

  Lemma step_event:
  forall s1 e s1', Step sem s1 (e :: nil) s1' ->
  forall s2 s2',   Step sem' s2 (e :: nil) s2' ->
  forall s3 M, match_states M s1 s2 s3    ->
  exists s3' M', Plus sem'' s3 (e :: nil) s3' /\ (* using Plus here because we know if an event is emitted then we've done at least one step *)
              match_states M' s1' s2' s3'.
  Proof.
    intros s1 e s1' step_s1 s2 s2' step_s2 s3 M match_st.
    remember (id s3) as s3'; simpl in Heqs3'; destruct s3' as [mem3 regs3 [pc3_val pc3_tag] internal3 cn3].
    rewrite Heqs3' in match_st; rewrite Heqs3'. pose proof (esym Heqs3') as eq_s3. clear Heqs3'.
    inversion step_s2;
      unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
    all: unfold_all; try unfold_match; unfold_all.
    all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
    (* gets rid of cases with no events *)
    1-6, 8: (exfalso; clear -NEXT Heqa0 Heqa4 Heqa7; repeat (unfold_all || unfold_match); done).
    3: (exfalso; clear -CALL; unfold run_syscall in *; repeat (unfold_all || unfold_match); done).
    all: (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
    all: (assert (ts0 = (ts (mvec None)) ) by
             (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
              destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
    all: (unfold mvec in *; assert (ti1 = ti0) by
                (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                 destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
    all: unfold check_belong, belong, reg_clear_list in *.
    all: repeat (unfold_all || unfold_match).
    all: destruct tpc0; repeat (unfold_all || unfold_match); simpl in *.
    all: convert_eq_op.
    all: unfold is_jump, check_ret in *; try (repeat unfold_match; subst t1).
    all: unfold hshead in *; simpl in *.
    all: (inversion Heqa0); revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
    all: simpl in *.
    1: rename i1 into comp; rename color0 into comp'.
    2: rename i2 into comp; rename color0 into comp'.
    (* tidying up the hypothesis *)
    all: simpl in *.
    all: repeat
           (match goal with
              H: Some _ = getm (setm _ _ _) _ |- _ =>
                repeat (rewrite setmE in H; unfold as_word in H; simpl in H)
            end).
    all: repeat
           (match goal with
              H: Some _ = match (eq_op (_ (_ ((_ (_ ?a _)) _ _))) _) with _ => _ end,
                H' : Some _ = getm _ (as_word (_ ?a))
              |- _ => idtac a; unfold as_word in H'; rewrite ST in H; simpl in H', H; rewrite <- H' in H
            end).
    all: simpl in *.
    all: repeat (match goal with H: ?a = ?a |- _ => clear H end).
    (* we branch on which side is strongly related to s3 *)
    all: destruct match_st as [M ? ? ? common strong weak |M ? ? ? common weak strong];
      (* in each case, we keep only one step from s1 (the most useful for the case being treated) *)
      [match (type of step_s1) with
         (_ _ _ _ _ _ ?ev _) =>
           remember ev as t;
           destruct step_s1 as [s1 ? s1' step_s1 allowed | s1 ? s1' step_s1 _];
           [exfalso;
            destruct strong as [? ? ? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor s_reg_cor s'_reg_cor mem_match reg_match];
            eapply Machine.Intermediate.fdisjoint_partition_notinboth;
            [inversion Hmergeable_ifaces as [[_ fdisj] _]; exact fdisj | exact allowed | unfold side_of in *; unfold_match' side_eq]
           | ]; subst t
       end
      |match (type of step_s1) with
         (_ _ _ _ _ _ ?ev _) =>
           assert (step_2: step2 tt s1 ev s1');
           [remember ev as t; destruct step_s1 as [s1 ? s1' step_s1 allowed | s1 ? s1' _ step_s1]; subst t; exact step_s1
           | clear step_s1; rename step_2 into step_s1]
       end].
    repeat
      match goal with
        H: Some ?a = match ?cond with true => Some ?b | false => Some ?c end |- _ =>
          assert (a = if cond then b else c); [destruct cond; inversion H; try congruence| clear H]
      end.
    all: inversion step_s1;
      unfold next_state_updates, next_state_do_updates, next_state_updates_and_pc,
      next_state, transfer, instr_rules, LRC.transfer, LRC.instr_rules in *.
    all: unfold_all; try unfold_match; unfold_all.
    all: try (exfalso; clear -CALL; unfold run_syscall in *; repeat (unfold_all || unfold_match)). (* eliminate alloc cases *)
    all: match goal with
         | H: @eq (ivec lrc_tags) _ _ |- _ => rename H into ivec_eq
         end.
    all: try (exfalso; unfold mvec0 in ivec_eq; clear- ivec_eq; repeat unfold_match' ivec_eq; done). (* eliminate many uncoherent cases *)
    all: (assert (tpc1 = tpc0) by (clear -ivec_eq; unfold_match' ivec_eq); subst tpc1).
    all: destruct tpc0.
    all: assert (eqo1: OP o1 = op (mvec0 None)) by (try subst o1; unfold mvec0 in *; clear -ivec_eq; unfold_match' ivec_eq).
    all: unfold mvec0 in eqo1; simpl in eqo1; inversion eqo1; subst o1.
    all: (assert (ts0eq: ts0 = (ts (mvec0 None)) ) by
           (unfold mvec0 in *; simpl; clear -ivec_eq; unfold_match' ivec_eq; try (inversion ivec_eq; subst b);
            eapply ivec_eq_inv in ivec_eq; destruct ivec_eq as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto);
          unfold mvec0 in ts0eq; simpl in ts0eq; subst ts0).
    all: (unfold mvec0 in *; assert (ti1 = ti0) by
                (clear -ivec_eq; unfold_match' ivec_eq; try (inversion ivec_eq; subst b); eapply ivec_eq_inv in ivec_eq;
                 destruct ivec_eq as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
    all: unfold check_belong, belong, reg_clear_list in *.
    all: repeat
           let pl := fresh "pl" in
           let pr := fresh "pr" in
           match goal with
           | p : _ * option event |- _ =>
               match goal with
               | H : Some p = _ |- _ =>
                   assert (tmp: p.2 = None) by (clear -H; repeat (unfold_all || unfold_match));
                   destruct p as [pl pr]; inversion tmp; clear tmp; simpl in *; try subst pl; try subst pr
               end
           end.
    all: try simplify_some.
    all: try (exfalso; clear -NEXT; repeat (unfold_all || unfold_match); done). (* eliminate all remaining cases with no events *)
    all: unfold reg_clear_list_aux in CLEAR; unfold_all.
    2, 4, 5, 7: exfalso; 
    repeat ( match goal with | p : _ * option event |- _ => destruct p end); simpl in *;
    repeat (unfold_all || unfold_match). (* eliminate cases with the wrong events *)
    all: repeat
           match goal with
             H: Some ?a = match ?cond with true => Some ?b | false => Some ?c end |- _ =>
               assert (a = if cond then b else c); [destruct cond; inversion H; try congruence| clear H]
           end.
    all: repeat (unfold_all || unfold_match).
    all: subst color color0; try subst i3; destruct e0, e; simpl in *; subst rcom_value0.
    all: unfold is_jump, check_ret, build_tpc in *; try (repeat unfold_match; subst t1).
    all: convert_eq_op.
    all: unfold_match' ivec_eq; inversion ivec_eq as [tag_mem_w0].
    all: try (match goal with
                H : @eq (ovec lrc_tags _) _ _ |- _ => inversion H; clear H
              end).
    all: revert ST ST0 eq_s3; subst; intros ST ST0 eq_s3; simpl in *. (* trick to keep an equality on s1 and s3 *)
    1-2: rename i1 into comp.
    3-4: rename i2 into comp.
    (* We now need to branch on which state is strongly related to s3 next (i.e. comp', the color of the next compartment) *)
    all: destruct (in_mem comp' (ssrbool.mem (domm ip))) eqn: side_comp';
      [ assert (ip_comp': comp' \in domm ip); [rewrite side_comp'; trivial|]
      | assert (ic_comp': comp' \in domm ic); [admit |]]; clear side_comp'. (* need hypothesis on the colors contained by memory *)
    all: inversion strong as [? ? ? wf_m comp_num pc_s'_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
    all: inversion common as [? ? ? ? ? ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 col_mem1]]]]]
                          [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 col_mem2]]]]]
                          [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 col_mem3]]]]] code_left code_right].
    all: subst s s' s0 s4 s5 m m0.
    all: rewrite ST in tag_pc2; inversion tag_pc2; subst n0 c0; clear tag_pc2.
    (* Steps needed in each cases: *)
    (* 1/ deduce beforehand the equalities on s3 needed to proceed, *)
    (* 2/ unfold to show that a step can be done from s3, *)
    (* 3/ show that match_state hold for the new states. *)
    all: repeat match goal with
             |- context[vala (match ?cond with true => ?a | false => ?b end)] =>
               assert (tmp: vala (match cond with true => a | false => b end) = (match cond with true => vala a | false => vala b end));
               [ clear; destruct cond; simpl; done | rewrite tmp; clear tmp]
           end; simpl.
    all: ((destruct pc_s'_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s'_s3]
          || destruct pc_s'_s3 as [? ? ? eq_none|s2 s3 ? ? _ eq_off pc_s'_s3]);
          [exfalso; subst; simpl in *; (rewrite eq_none in PC) || (rewrite eq_none in PC0); done |]).
    (*
    (* deducing all needed equalities for the different cases *)
    all:
      (match (type of strong) with
       | strong_equiv Left _ _ _ =>
           repeat
             (match goal with
                H : Some ?a = getm reg0 _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
              end);
           match (type of step_s2) with
           | step_me s2 _ (Some (ERet _ _ _)) => deduce_equality RW0
           | step_me s2 _ (Some (ECall _ _ _ _)) =>
               deduce_equality OLD0;
               subst s1; unfold side_of in *; unfold_match' side_eq; simpl in *;
               deduce_equality PC0
           end
       | strong_equiv Right _ _ _ =>
           repeat
             (match goal with
                H : Some ?a = getm reg _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
              end);
           match (type of step_s2) with
           | step_me s2 _ (Some (ERet _ _ _)) => deduce_equality RW
           | step_me s2 _ (Some (ECall _ _ _ _)) =>
               deduce_equality OLD;
               subst s2; unfold side_of in *; unfold_match' side_eq; simpl in *;
               deduce_equality PC
           end
       end)
     *)
      (*
      match (type of ip_comp') with
      | _ \in domm ip =>
      | _ \in domm ic =>
      end
       *)
    + (* return from comp in P to comp' in P *)
      repeat
        (match goal with
           H : Some ?a = getm reg0 _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
         end).
      deduce_equality RW0.
      subst s1. unfold side_of in *. unfold_match' side_eq. simpl in *.
      deduce_equality PC0.
      assert (Meq: exists top M', M = top :: M').
      { destruct vt_match10 as [ret_eq stack_prop]. unfold color_of in stack_prop.
        subst t10. simpl in stack_prop. destruct stack_prop as [top [col top_in]].
        destruct M; eauto. inversion top_in. }
      destruct Meq as [top [M' M_eq]]. destruct a41 as [xt xv].
      destruct vt_match10 as [ret_eq stack_prop]. unfold color_of in stack_prop.
      subst t10. simpl in stack_prop. destruct stack_prop as [s2val [comp'' triple_in]].
      match (type of triple_in) with (_ ?t _) => assert (top = t); [|subst top] end. 
      { inv tag_pc1. simpl in *. subst.
        clear- wfst triple_in. destruct triple_in as [?| is_in]; auto. exfalso.
        remember (Nat.pred n) as n'. assert (n'_ineq: S n' >= n) by (subst; clear; induction n; eauto).
        clear Heqn'.
        revert is_in. revert n'_ineq. revert w0 s2val v11 comp'' n'.
        inversion wfst; subst; clear - WF_ST; simpl; unfold Init.Nat.pred, "+", addn_rec; rewrite Nat.add_1_r.
        all: induction WF_ST; intros a v b col n' n'_ineq is_in; inversion is_in.
        all: try (inversion H; subst n; (assert false; [|done]); rewrite <- (ltn_subrR 0 (S n')); unfold subn, subn_rec, Nat.sub;
                  unfold addn, addn_rec in n'_ineq; rewrite Nat.add_1_r in n'_ineq; done).
        all: eapply (IHWF_ST _ _ _ _ _ _ H). }
      assert (comp'' = comp'); [|subst comp''].
      { clear - wfst M_eq Heqa7 tag_mem_w0. inversion wfst; subst M; inv H0;
        unfold points_to_comp_code' in PTS_CODE1; oapp_False; simpl in *; rewrite <- Heqa7 in HeqH; simplify_some;
        destruct PTS_CODE1 as [col ?]; rewrite <- tag_mem_w0 in col; simpl in col; auto. }
      inversion wfst; subst M; try (inv H0; done); simpl in *.
      2: { exfalso. inv H14. clear - SIDE ip_comp' Hmergeable_ifaces.
           eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
           inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. }
      (* pose proof (wf_m _ _ _ _ _ _ triple_in (Logic.eq_refl) eq_off') as cap_prop.*) (* we don't need both wf_m *and* wfst *)
      inversion H14. subst v13 n n0 s2val v15 C st. clear H20 H14.
      unfold points_to_comp_code in PTS_CODE3. oapp_False.
      eexists. exists M'.
      split.
      * eapply (plus_left _ [:: ERet comp rcom_value1 comp'] ). try eapply step_jump; eauto.
        -- rewrite eq_s3 in vt_eq11. exact vt_eq11.
        -- inversion vt_match11; subst; revert H11; try decode_instr_eq.
        -- rewrite eq_s3 in vt_eq10. exact vt_eq10.
        -- unfold reg_clear_list, reg_list. simpl. unfold as_word. subst. simpl.
           repeat
             (match goal with
              | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
              end). trivial.
        -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
           unfold evi in *. simpl. unfold_bind.
           deduce_reg reg_match. subst v11. simpl in *.
           rewrite <- HeqH11. simpl. rewrite eq_s3 in tag_pc3. simpl in tag_pc3.
           rewrite tag_pc3. rewrite eq_refl. simpl.
           destruct PTS_CODE3 as [col_a10 code_a10]. destruct a10 as [va10 ta10]. destruct ta10.
           simpl in col_a10. rewrite col_a10. simpl. rewrite <- Heqa10. simpl.
           destruct a22. unfold is_other in *. unfold_match' Heqa50. simpl in *.
           subst taga. inversion vt_match9 as [? _]. subst t9. simpl.
           unfold "+", addn_rec. rewrite Nat.add_1_r. simpl. rewrite eq_refl. simpl.
           unfold updm. unfold as_word. simpl in *.
           (*automatically rewrite regs3 registers*)
           repeat
             (repeat
                (match goal with
                 | H: getm _ ?w = _  |- context[getm _ ?w] => rewrite H; simpl
                 end);
              (*automatically transforms setm in if (_ == _) then _ else _*)
              repeat rewrite setmE; simpl;
              (*destruct the (_ == _) condition *)
              try
                (let cond := fresh "cond" in
                 match goal with
                 | |- context[@eq_op ?t ?a ?r] =>
                     remember (@eq_op t a r) as cond; destruct cond;
                     [convert_eq_op; simpl in *|]; simpl
                 end)).
           all: inversion Heqa0; subst rcom_value1; rewrite H10 in Heqa5; simplify_some; destruct x; destruct H11; subst; simpl.
           12: reflexivity.
           all: unfold as_word in *; simpl in *.
           all: (match (type of vt_eq10) with
                 | ?ls = ?rs =>
                     revert vt_eq10;
                     (match goal with
                        Heq: ls = Some (?a) |- _ =>
                          intro vt_eq10; rewrite Heq in vt_eq10; simplify_some; subst; simpl
                      end)
                 end).
           all: repeat (rewrite setmxx || (rewrite (setmC _ ((addw _ _)@_)); [|done]) ).
           all: trivial.
        -- eapply star_refl.
        -- reflexivity.
      * admit.
    + (* return from comp in P to comp' in C *)
      repeat
        (match goal with
           H : Some ?a = getm reg0 _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
         end).
      deduce_equality RW0.
      admit.
    + (* return from comp in C to comp' in P *)
      repeat
      (match goal with
         H : Some ?a = getm reg _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
       end).
      deduce_equality RW.
      admit.
    + (* return from comp in C to comp' in C *)
      repeat
      (match goal with
         H : Some ?a = getm reg _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
       end).
      deduce_equality RW.
      admit.
    + (* call from comp in P to comp' in P *)
      repeat
      (match goal with
         H : Some ?a = getm reg0 _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
       end).
      deduce_equality OLD0.
      subst s1. unfold side_of in *. unfold_match' side_eq. simpl in *.
      deduce_equality PC0.
      (* quick proof that v12 (s3) is a JAL offseted from i0 *)
      unfold_match' Heqa2.
      inversion vt_match11; try subst i0; revert H13; decode_instr_eq; intro H13.
      { destruct (H13 imm0); auto. }
      { inversion H13. subst imm0 pc'0. unfold alloc_empty in *. subst. simpl in alloc_mem_s1.
        assert (sw_eq: @swcast _ (word_size mt) (@word_of_nat (imm_size mt) alloc_label) = word_of_nat alloc_label).
        { admit. } simpl in sw_eq.
        rewrite <- sw_eq in alloc_mem_s1. rewrite <- Heqa61 in alloc_mem_s1. inversion alloc_mem_s1. }
      inversion H13. subst imm1. clear H13. subst pc'0. rewrite H15 in Heqa61. simplify_some. simpl in *.
      destruct d as [vd td]. rename H16 into eq_next_pc.
      assert (exists off', offset1 comp' = Some off') as [off' eq_off'].
      { eapply (rwP dommP). rewrite offset1_domm. trivial. }
      destruct ((fst (code_left _ vd td off' _ ip_comp' eq_off' H17 (esym (congr1 color tag_mem_w0)))) (H15))
        as [d [dmatch deq]].
      assert (imm'eq: @swcast _ (word_size mt) imm' = (swcast imm0 + as_word off')%w) by admit. (* need more hypothesis *)
      rewrite imm'eq in eq_next_pc. rewrite eq_next_pc in deq. simplify_some.
      remember (((pc1 + 1)%w@(Ret n), (pc0 + 1)%w@(Ret n1), (pc0 + 1 + as_word off')%w@(Ret n1), comp') :: M) as M'.
      eexists. exists M'.
      split.
      * eapply (plus_left _ [:: ECall _ _ _ _] ). eapply step_jal; eauto.
        -- rewrite eq_s3 in vt_eq11. exact vt_eq11.
        -- simpl. exact H14.
        -- rewrite eq_s3 in vt_eq10. exact vt_eq10.
        -- unfold reg_clear_list, reg_list. simpl. unfold as_word. subst. simpl.
           repeat
             (match goal with
              | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
              end). trivial.
        -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
           unfold evi in *. simpl. unfold_bind.
           deduce_reg reg_match. rewrite imm'eq. rewrite eq_next_pc. simpl.
           rewrite eq_s3 in tag_pc3. simpl in tag_pc3. rewrite tag_pc3. simpl. rewrite eq_refl. simpl.
           simpl in *. rewrite <- tag_mem_w0. rewrite <- Heqa8. simpl.
           destruct a21 as [va21 ta21]. unfold is_other in *. destruct ta21; simpl in Heqa49; inversion Heqa49.
           inversion vt_match9 as [? _]; subst t9. simpl. rewrite <- Heqa35. simpl.
           unfold updm. unfold as_word. simpl in *.
           (*automatically rewrite regs3 registers*)
           repeat
             (repeat
                (match goal with
                 | H: getm _ ?w = _  |- context[getm _ ?w] => rewrite H; simpl
                 end);
              (*automatically transforms setm in if (_ == _) then _ else _*)
              repeat rewrite setmE; simpl;
              (*destruct the (_ == _) condition *)
              try
                (let cond := fresh "cond" in
                 match goal with
                 | |- context[@eq_op ?t ?a ?r] =>
                     remember (@eq_op t a r) as cond; destruct cond;
                     [convert_eq_op; simpl in *|]; simpl
                 end)).
           destruct x as [vx tx]. inversion H13. subst tx vx.
           reflexivity.
        -- eapply star_refl.
        -- unfold evi in Heqa21, Heqa. repeat unfold_bind. inv Heqa. inv Heqa21. simpl.
           simpl in *. rewrite H12 in Heqa43. simplify_some. rewrite H16. reflexivity.
      * admit.
    + (* call from comp in P to comp' in C *)
      repeat
      (match goal with
         H : Some ?a = getm reg0 _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
       end).
      deduce_equality OLD0.
      unfold_match' Heqa2.
      rename Heqa40 into new_pc_s2.
      (* need new hypothesis here to get a "eq_pc_next" for s3 *)
      admit. 
    + (* call from comp in C to comp' in P *)
      repeat
      (match goal with
         H : Some ?a = getm reg _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
       end).
      deduce_equality OLD.
      (* need new hypothesis here to get a "eq_pc_next" for s3 *)
      admit.
    + (* call from comp in C to comp' in C *)
      repeat
      (match goal with
         H : Some ?a = getm reg _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
       end).
      deduce_equality OLD.
      subst s2. unfold side_of in *. unfold_match' side_eq. simpl in *.
      unfold color_of in Heqa5. simpl in *.
      assert (side_eq': true = (comp \in domm ic)).
      { assert (comp_incl: comp \in (domm ic) \/ comp \in (domm ip)) by admit. (* need hypothesis *)
        destruct comp_incl as [Hl | Hr]. rewrite Hl. trivial. rewrite Hr in Heqa5. inversion Heqa5. }
      (* todo: fix *)
      deduce_equality PC.
      (* quick proof that v11 (s3) is a JAL offseted from i0 *)
      unfold decode_match in *. revert vt_match10. decode_instr_eq.
      intro v10_prop. unfold_all; try (subst; rewrite <- Heqa3 in Heqa4; inversion Heqa4; done).
      match (type of v10_prop) with
        match (?cond) with _ => _ end =>
          destruct cond eqn:X; try (subst; rewrite <- Heqa3 in Heqa4; simplify_some; rewrite H1 in X; inversion X; done)
      end.
      rename Heqa55 into eq_next_pc. subst pc'0.
      match (type of v10_prop) with | match ?cond with _ => _ end => destruct cond eqn: condeq end.
      { destruct (orb_prop _ _ condeq) as [eqalloc | eqalloc]; pose proof (esym eqalloc); convert_eq_op; subst;
          unfold alloc_empty in *; rewrite alloc_mem_s1 in eq_next_pc; inversion eq_next_pc. }
      assert (pc_eq_imm: (@swcast _ (word_size mt) i2) = addw (swcast imm0) (as_word off)).
      { subst. admit. } (* probably doable with slight lemma/hypothesis on off *)
      (* proof that the next PC points to code *)
      pose proof (bnz_s1 _ _ PC0) as JALcond. revert JALcond. decode_instr_eq. intro JALcond.
      destruct JALcond as [[x [next_pc_content' next_pc_code]] | imm_alloc_eq ]; auto.
      2: { exfalso. subst imm0.
           assert (swcast_alloc: (@swcast _ (word_size mt) (@word_of_nat (imm_size mt) alloc_label)) = ((word_of_nat alloc_label))).
           { unfold swcast, word_of_nat. simpl.
             unfold alloc_label. rewrite div.modn_small. trivial. trivial. }
           rename eq_next_pc into H'.
           rewrite swcast_alloc in H'. rewrite alloc_mem_s1 in H'. inversion H'. }
      rewrite <- eq_next_pc in next_pc_content'. simplify_some.
      destruct x as [vx tx]. inversion ivec_eq as [tx_eq].
      assert (exists off', offset1 comp' = Some off') as [off' eq_off'] by admit. (* need hypothesis on offset domain *)
      destruct ((fst (code_left _ vx tx off' _ ip_comp' eq_off' next_pc_code (esym (congr1 color tx_eq)))) (esym eq_next_pc))
        as [d [dmatch deq]].
      (* todo: eexists + unfolding. *)
      admit.
  Admitted.


        
  Lemma step_silent_strong1:
    forall s1 s1', Step sem s1 E0 s1' ->
    forall s2 s3 M, strong_equiv Left M s1 s3 ->
               weak_equiv Right M s2 s3 ->
               common_equiv M s1 s2 s3 ->
    exists s3' M', Plus sem'' s3 E0 s3' /\ (* Using Plus to ensure the strongly related states take a step *)
              strong_equiv Left M' s1' s3' /\
              weak_equiv Right M' s2 s3' /\
              common_equiv M' s1' s2 s3'.
  Proof.
    intros s1 s1' step_s1 s2 s3 M strong weak common. simpl in step_s1.
    remember E0 as t.
    destruct step_s1 as [s1 ? s1' step_2 allowed | s1 ? s1' step_1 step_2]; subst t.
    - unfold allowed_UB in *.
      inversion strong as [m ? ? wf_m comp_num pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor s_reg_cor s'_reg_cor mem_match reg_match].
      subst m s s'.
      exfalso. eapply Machine.Intermediate.fdisjoint_partition_notinboth.
      * inversion Hmergeable_ifaces as [[_ fdisj] _]. exact fdisj.
      * exact allowed.
      * unfold side_of in *. unfold_match' side_eq.
    - remember (id s3) as s3'; simpl in Heqs3'; destruct s3' as [mem3 regs3 [pc3_val pc3_tag] internal3 cn3].
      rewrite Heqs3' in strong weak common; rewrite Heqs3'. pose proof (esym Heqs3') as eq_s3.
      inversion strong as [? ? ? wf_m comp_num pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor s_reg_cor s'_reg_cor mem_match reg_match].
      inversion common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst
                             [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 end_s1]]]]
                                 [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 end_s2]]]]
                                 [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 end_s3]]]] code_left code_right].
      subst s s' s0 s4 s5 m m0.
      inversion step_1; unfold step1;
        unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
      all: unfold_all; try unfold_match; unfold_all.
      all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
      all: try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
      all: try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
      all: try (assert (ts0 = (ts (mvec None)) ) by
               (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
      all: try (unfold mvec in *; assert (ti1 = ti0) by
                  (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                   destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).      
      all: try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                  (match goal with
                   | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                     => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                       rewrite inst in instr_is_halt; done end) |
                  simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
      all: unfold check_belong, belong, reg_clear_list in *.
      all: simpl in *; unfold_all.
      7-8: try (match (type of Heqa2) with
                  (_ = match ?m ?w with _ => _ end)
                  => eapply (@modusponens (exists res, m w = Some res /\ (is_code (taga res))));
                    [|intros [res [res_eq res_code]]; rewrite res_eq in Heqa2]
                end).
      11: remember (mem0 pc') as next_pc_content; destruct next_pc_content.
      all: try (match goal with
                  |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
      all: convert_eq_op.
      all: unfold is_jump in *; try (unfold_match; subst t1).
      all: unfold hshead in *; simpl in *.
      all: try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
      all: try (pose proof (esym Heqa3) as PC; clear Heqa3).
      all: try (match goal with c: Component.id |- _ => rename c into color end).
      all: try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                [exfalso; subst; simpl in *; rewrite eq_none in PC; done |]).
      all: try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                subst c0).
      all: try (destruct tpc0; unfold_all).
      all: try (unfold compatible in *; rewrite eq in m_compat).
      all: try rewrite m_compat in side_eq.
      + eexists; exists M. simpl.
        split.
        * eapply (plus_left _ [::]). try eapply step_nop; eauto.
          -- eapply (etrans _ PC).
          -- decode_instr_eq.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. simpl. unfold_bind.
             deduce_reg reg_match .
             assert (mem3 (addw pc3_val onew) = mem0 (addw pc0 onew)). eapply (etrans _ (esym Heqi')).
             rewrite eq_s3. simpl. rewrite H1 Heqi'. simpl. rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3.
             clear tag_pc1. rewrite ST. unfold color_of. simpl. rewrite eq_refl. simpl.
             unfold check_belong, belong. rewrite eq_refl. simpl. trivial.
          -- eapply star_refl.
          -- done.
        * eapply (preserves_equiv_left_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); eauto.
          -- rewrite ST. simpl. done.
          -- rewrite eq_s3. simpl. done.
          -- rewrite ST. eapply same_pc_normal; simpl; eauto.
             ++ subst. unfold color_of in * . simpl in *. exact eq_off.
             ++ subst. simpl in *. rewrite pc_s1_s3. simpl. rewrite <- (addwA pc0 _).
                rewrite (addwC (as_word _) onew). rewrite addwA. done.
      + eexists; exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_const; eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
          -- eapply (etrans _ (OLD)).
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match.
             assert (mem3 (addw pc3_val onew) = mem0 (addw pc0 onew)). eapply (etrans _ (esym Heqi')).
             rewrite eq_s3. rewrite H1 Heqi'. simpl. unfold check_belong, belong. rewrite eq_refl. simpl.
             rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. rewrite ST. unfold color_of. simpl. rewrite eq_refl. simpl.
             (let H := fresh "H" in
               let v := fresh "v" in
               match goal with
               | |- context [updm ?r ?w _] =>
                   assert (exists v, (r w = Some v)) as [v H]; [| unfold updm; rewrite H; clear H] end).
             { subst. deduce_reg reg_match. eauto. }
             simpl. done. 
          -- eapply star_refl.
          -- done.
        * eapply preserves_equiv_left_reg_write with (r := r) (v := (swcast n0)@Other) (v' := (swcast n0)@Other); auto.
          eapply (preserves_equiv_left_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); eauto.
          all: try (split; done).
          -- subst. simpl. eapply same_pc_normal.
             simpl. eauto.
             subst. unfold color_of in *. simpl in *. eauto.
             simpl in *. rewrite pc_s1_s3. simpl. rewrite <- (addwA pc0 _). rewrite (addwC (as_word _) onew). rewrite addwA. done.
          -- unfold updm. simpl.
             rewrite ST OLD. simpl. done.
          -- unfold updm. simpl. subst. deduce_reg reg_match. done.
          -- simpl. rewrite ST. simpl. done.
          -- subst. simpl. done.
      + deduce_equality OLD.
        deduce_equality R1W.
        eexists. exists M. simpl.
        remember (@eq_op (Ord.eqType _) r2 r1) as cond.
        split.
        * eapply (plus_left _ [::]); try eapply step_mov. eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match.
             subst s3 s1. simpl in *. simpl in *.
             unfold side_of in side_eq. unfold_match' side_eq. deduce_equality Heqi'.
             rewrite vt_eq1. simpl.
             unfold check_belong, belong. rewrite eq_refl. simpl.
             unfold updm. rewrite vt_eq0. simpl.
             try rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. try rewrite ST. unfold color_of. simpl. rewrite eq_refl. simpl.
             repeat rewrite setmE. simpl in Heqcond.
             rewrite <- Heqcond. destruct cond.
             ++ assert (r_eq: r2 = r1) by (eq_op_to_eq). simpl in *. simpl. trivial. 
             ++ deduce_reg reg_match. done.
          -- destruct cond; eapply star_refl.
          -- done.
        * inversion vt_match0 as [? _]. subst t0. unfold_all.
          rewrite ST in Heqa11. simpl in Heqa11. rewrite R1W in Heqa11. simplify_some.
          rewrite ST. simpl. remember (if is_address t1 then Invalidated else Other) as new_t1.
          eapply preserves_equiv_left_reg_write with (r := r2) (v := w1@t1) (v' := v1@t1).
          eapply preserves_equiv_left_reg_write with (r := r1) (v := w1@new_t1) (v' := (v1@new_t1)).
          eapply (preserves_equiv_left_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); auto. eauto.
          all: simpl; try trivial. 
          all: unfold updm.
          all: try done.
          -- subst. simpl. eapply same_pc_normal.
             simpl. eauto.
             simpl. eauto. simpl in *.
             rewrite pc_s1_s3. simpl. rewrite <- (addwA pc0 _). rewrite (addwC (as_word _) onew). rewrite addwA. done.
          -- split; auto. subst. destruct t1; simpl; auto. destruct vt_match0. auto.
          -- subst. destruct t1; simpl; auto.
          -- subst. destruct t1; simpl; auto.
          -- rewrite ST R1W. simpl. done.
          -- rewrite vt_eq0. done.
          -- destruct vt_match0. subst. unfold color_of in *. simpl in *. split; trivial.
          -- subst. simpl. eapply (s_reg_cor _ _ R1W).
          -- subst. simpl. eapply (s'_reg_cor _ _ vt_eq0).
          -- repeat rewrite setmE. rewrite <- Heqcond. destruct cond; subst; simpl; try done.
             rewrite OLD. simpl. done.
          -- repeat rewrite setmE. rewrite <- Heqcond. destruct cond; subst; simpl; try done.
             deduce_reg reg_match. done.
          -- simpl. subst. trivial.
          -- subst. simpl. trivial.
      + deduce_equality OLD.
        deduce_equality R1W.
        deduce_equality R2W.
        remember (@eq_op (Ord.eqType _) r2 r1) as cond.
        remember (@eq_op (Ord.eqType _) r3 r1) as cond1.
        remember (@eq_op (Ord.eqType _) r3 r2) as cond2.
        destruct vt_match0 as [? match_t1]. subst t0. destruct t1; unfold is_other in *; try congruence. subst v1.
        destruct vt_match1 as [? match_t3]. subst t2. destruct t3; unfold is_other in *; try congruence. subst v2.
        eexists. exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_binop. eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- rewrite eq_s3 in vt_eq1. eauto.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match.
             unfold side_of in side_eq. unfold_match' side_eq. subst s1 s3. simpl in *. deduce_equality Heqi'.
             rewrite vt_eq2. simpl.
             unfold check_belong, belong. rewrite eq_refl. simpl.
             unfold updm. rewrite vt_eq0. simpl.
             try rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. try rewrite ST. unfold color_of. simpl. rewrite eq_refl. simpl.
             repeat rewrite setmE. simpl in Heqcond, Heqcond1, Heqcond2. unfold stack_value in *. simpl in *. rewrite <- vt_eq0.
             rewrite <- Heqcond. destruct cond; simpl.
             ++ assert (r_eq: r2 = r1) by (eq_op_to_eq). rewrite r_eq in vt_eq1. rewrite vt_eq1. simpl.
                repeat rewrite setmE. 
                rewrite <- Heqcond2. destruct cond2; simpl; try done.
                rewrite <- Heqcond1. destruct cond1; simpl; try done.
                rewrite vt_eq. simpl. done. 
             ++ rewrite vt_eq1. simpl. repeat rewrite setmE.
                rewrite <- Heqcond2. destruct cond2; simpl; try done.
                rewrite <- Heqcond1. destruct cond1; simpl; try done.
                deduce_reg reg_match. done.
          -- eapply star_refl.
          -- done.
        * rewrite ST in Heqa11. simpl in Heqa11. rewrite R1W in Heqa11. simplify_some.
          assert (eq_a: a = (if cond then w1 else w2)@Other).
          { repeat rewrite setmE in Heqa12. simpl in *. rewrite <- Heqcond in Heqa12.
            subst s1. rewrite R2W in Heqa12. destruct cond; simplify_some; done. }
          destruct a as [w' t']. inversion eq_a. clear eq_a. subst t'. rewrite <- H1. simpl.
          remember (binop_denote op0 w1 w2) as new_w.
          eapply preserves_equiv_left_reg_write with (r := r3) (v := new_w@Other) (v' := new_w@Other).
          eapply preserves_equiv_left_reg_write with (r := r2) (v := w'@Other) (v' := w2@Other).
          eapply preserves_equiv_left_reg_write with (r := r1) (v := w1@Other) (v' := w1@Other).
          eapply (preserves_equiv_left_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); auto. eauto.
          all: simpl.
          all: try (match goal with | |- ( @Logic.eq (@Symbolic.state _ _ _) ?s _) => trivial end).
          all: simpl.
          all: try (match goal with
                      |- context[updm _ _] =>
                        unfold updm;
                        simpl; try ((rewrite ST OLD) ||  (rewrite ST R1W) || (rewrite ST MEM1));
                        try (rewrite vt_eq1 || rewrite vt_eq || rewrite vt_eq0); simpl; done
                    end).
          all: try subst t2'; simpl; trivial.
          all: try trivial.
          -- rewrite ST. eapply same_pc_normal; simpl; eauto.
             ++ subst. unfold color_of in *. simpl in *. eauto.
             ++ rewrite pc_s1_s3 ST. simpl. rewrite <- (addwA pc0 _). rewrite (addwC (as_word _) onew). rewrite addwA. done.
          -- split; auto.
          -- split; auto. subst w'. destruct cond; auto. convert_eq_op. rewrite R1W in R2W. simplify_some. done.
          -- unfold updm. repeat rewrite setmE. simpl in *. rewrite <- Heqcond.
             destruct cond; simpl; try done. rewrite R2W. simpl. done.
          -- unfold updm. repeat rewrite setmE. simpl in *. rewrite <- Heqcond.
             destruct cond; simpl; try done. rewrite vt_eq1. simpl. done.
          -- split; auto.
          -- unfold updm. repeat rewrite setmE.
             simpl in *. rewrite <- Heqcond2.
             destruct cond2; simpl; try done. 
             simpl in *. rewrite <- Heqcond1.
             destruct cond1; simpl; try done. rewrite OLD. simpl. done.
          -- unfold updm. repeat rewrite setmE.
             simpl in *. rewrite <- Heqcond2.
             destruct cond2; simpl; try done. 
             simpl in *. rewrite <- Heqcond1.
             destruct cond1; simpl; try done. rewrite vt_eq. simpl. done.
          -- subst. done.
          -- subst. done.
      + rewrite ST in tag_pc1. inversion tag_pc1. subst n1 i1.
        deduce_equality R1W.
        deduce_equality MEM1.
        deduce_equality OLD.
        destruct vt_match as [? match_t]. subst t. destruct t1; unfold is_other in *; try congruence. subst v0.
        eexists; exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_load; eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- rewrite eq_s3 in vt_eq1. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_bind. deduce_reg reg_match.
             assert (mem3 (addw pc3_val onew) = mem0 (addw pc0 onew)). eapply (etrans _ (esym Heqi')).
             rewrite eq_s3. rewrite H1 Heqi'. simpl. unfold check_belong, belong. rewrite eq_refl. simpl.
             destruct vt_match0. subst t0. simpl. rewrite eq_refl. simpl.
             try rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. try rewrite ST. rewrite eq_refl. simpl.
             subst s3.
             rewrite vt_eq. simpl. unfold updm. rewrite vt_eq. simpl. rewrite vt_eq0. simpl.
             repeat rewrite setmE. unfold stack_value in *. simpl in *.
             remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in Heqcond.
             rewrite <- Heqcond. destruct cond.
             ++ assert (r_eq: r2 = r1) by (eq_op_to_eq). simpl. reflexivity. 
             ++ rewrite vt_eq1. simpl. done. 
          -- eapply star_refl.
          -- done.
        * simpl in *.
          remember (if is_address vtag1 then Invalidated else Other) as new_t2.
          rewrite ST in Heqa12, Heqa13. rewrite R1W in Heqa12. rewrite MEM1 in Heqa13.
          do 2 simplify_some. simpl.
          remember ({| vtag := new_t2; color := color; entry := entry1; is_code := false |}) as t2'.
          eapply preserves_equiv_left_reg_write with (r := r2) (v := w2@vtag1) (v' := v1@vtag1).
          eapply preserves_equiv_left_mem_write with (v := w2@t2') (v' := v1@t2') (w := w1).
          eapply preserves_equiv_left_reg_write with (r := r1) (v := w1@Other) (v' := w1@Other).
          eapply (preserves_equiv_left_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); auto. eauto.
          all: simpl.
          all: try (match goal with | |- ( @Logic.eq (@Symbolic.state _ _ _) ?s _) => trivial end).
          all: simpl.
          all: try (match goal with
                      |- context[updm _ _] =>
                        unfold updm;
                        simpl; try ((rewrite ST OLD) ||  (rewrite ST R1W) || (rewrite ST MEM1));
                        try (rewrite vt_eq1 || rewrite vt_eq || rewrite vt_eq0); simpl; done
                    end).
          all: try subst t2'; simpl; trivial.
          all: try (subst; destruct vtag1; simpl; (exact Heqi' || auto); done).
          all: try done.
          -- rewrite ST. eapply same_pc_normal; simpl; eauto.
             ++ unfold color_of in *. subst. simpl in *. eauto.
             ++ rewrite pc_s1_s3 ST. simpl. rewrite <- (addwA pc0 _). rewrite (addwC (as_word _) onew). rewrite addwA. done.
          -- split; trivial. simpl. split; auto. subst. destruct vtag1; simpl; auto. destruct vt_match0. simpl in *.
             destruct H1. done.
          -- unfold side_of, color_of in side_eq. rewrite ST in side_eq. simpl in side_eq. unfold_match.
          -- rewrite ST. intros v' disj. destruct disj.
             ++ simpl in *. rewrite MEM1 in H. simplify_some. done.
             ++ rewrite vt_eq0 in H. simplify_some. destruct vt_match0. subst. auto.
          -- simpl. eexists; split; eauto. destruct vt_match0. subst. auto.
          -- simpl. eexists; split; eauto. destruct vt_match0. subst. simpl. rewrite MEM1. done.
             destruct vt_match0. subst. auto.
          -- destruct vt_match0. subst. split; auto. simpl in *. destruct H1. auto.
          -- subst. unfold memory_address_correctness in *. simpl in *. remember (@eq_op (Ord.eqType _) w2 w1) as cond.
             destruct vtag1; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond; destruct cond; simpl; convert_eq_op;
               try (eapply modusponens; [eapply (s_mem_cor _ _ _ MEM1)| simpl; intros [? [eq1 ?]]]; rewrite MEM1 in eq1;
                    simplify_some; simpl in *; inversion H);
               try (eapply (s_mem_cor _ _ _ MEM1)).
          -- subst. unfold memory_address_correctness in *. simpl in *. remember (@eq_op (Ord.eqType _) v1 w1) as cond.
             destruct vt_match0. subst t0.
             destruct vtag1; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond; destruct cond; simpl; convert_eq_op;
               try eapply (s'_mem_cor _ _ _ vt_eq0).
             all: try (eapply modusponens; [eapply (s'_mem_cor _ _ _ vt_eq0)| simpl; intros [? [eq1 ?]]]; rewrite vt_eq0 in eq1;
                  simplify_some; simpl in *; inversion H).
          -- unfold updm. rewrite setmE. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             rewrite <- Heqcond. destruct cond; try done. rewrite OLD. simpl. done.
          -- unfold updm. rewrite setmE. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             rewrite <- Heqcond. destruct cond; try done. subst. simpl. trivial. rewrite vt_eq1. simpl. subst. done.
      + rewrite ST in tag_pc1. inversion tag_pc1. subst n1 i1.
        deduce_equality R2W.
        deduce_equality R1W.
        deduce_equality OLD.
        destruct vt_match0 as [? match_t1]. subst t0. destruct t1; unfold is_other in *; try congruence. subst v1.
        eexists; exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_store; eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- rewrite eq_s3 in vt_eq1. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_bind. deduce_reg reg_match.
             assert (mem3 (addw pc3_val onew) = mem0 (addw pc0 onew)). eapply (etrans _ (esym Heqi')).
             rewrite eq_s3. rewrite H1 Heqi'. simpl. unfold check_belong, belong. rewrite eq_refl. simpl.
             destruct vt_match1. subst t3. simpl. rewrite eq_refl. simpl.
             subst s3.
             rewrite vt_eq0. simpl.
             (let H := fresh "H" in
               let v := fresh "v" in
               match goal with
               | |- context [updm ?r ?w _] =>
                   assert (exists v, (r w = Some v)) as [v H]; [| unfold updm; rewrite H; clear H] end).
             { subst. deduce_reg reg_match. eauto. }
             simpl.
             try rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. try rewrite ST. rewrite eq_refl. simpl.
             repeat rewrite setmE. unfold stack_value in *. simpl in *. rewrite <- vt_eq0.
             remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in Heqcond.
             rewrite <- Heqcond. destruct cond.
             ++ assert (r_eq: r2 = r1) by (eq_op_to_eq). rewrite r_eq in vt_eq. rewrite vt_eq. simpl. rewrite vt_eq1.
                simpl. done.
             ++ rewrite vt_eq. simpl. rewrite vt_eq1. simpl in *. done. 
          -- eapply star_refl.
          -- done.
        * simpl in *. remember ({| vtag := t2; color := color ; entry := entry0; is_code := false |}) as t2'.
          remember (if is_address t2 then Invalidated else Other) as new_t2.
          eapply preserves_equiv_left_reg_write with (r := r2) (v := w2@new_t2) (v' := v0@new_t2).
          eapply preserves_equiv_left_reg_write with (r := r1) (v := w1@Other) (v' := w1@Other).
          eapply preserves_equiv_left_mem_write with (v := w2@t2') (v' := v0@t2') (w := w1).
          eapply (preserves_equiv_left_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); auto. eauto.
          all: simpl.
          all: try (match goal with | |- ( @Logic.eq (@Symbolic.state _ _ _) ?s _) => trivial end).
          all: simpl.
          all: try (match goal with
                      |- context[updm _ _] =>
                        unfold updm;
                             simpl; try ((rewrite ST OLD) ||  (rewrite ST R1W) || (rewrite ST R2W));
                             try (rewrite vt_eq1 || rewrite vt_eq || rewrite vt_eq0); simpl; done
                    end).
          all: try subst t2'; simpl; trivial.
          all: try done.
          -- rewrite ST. eapply same_pc_normal; simpl; eauto.
             ++ unfold color_of in *. subst. simpl in *. eauto.
             ++ rewrite pc_s1_s3 ST. simpl. rewrite <- (addwA pc0 _). rewrite (addwC (as_word _) onew). rewrite addwA. done.
          -- inversion vt_match. subst. simpl. unfold data_match'. split; auto.
          -- subst. unfold color_of. simpl. trivial.
          -- subst. clear -side_eq. unfold color_of, side_of in *. inv side_eq. unfold_match.
          -- rewrite ST. intros v' disj. destruct disj.
             ++ simpl in *. rewrite OLD in H. simplify_some. done.
             ++ rewrite vt_eq1 in H. simplify_some. destruct vt_match1. subst. auto.
          -- simpl. eexists; split; eauto. destruct vt_match1. subst. auto.
          -- rewrite ST. simpl. eexists; split; eauto.
          -- subst. simpl. exact Heqi'.
          -- simpl. trivial.
          -- subst. simpl. eapply (s_reg_cor _ _ R2W).
          -- subst. simpl. destruct vt_match. subst. eapply (s'_reg_cor _ _ vt_eq).
          -- split; auto. subst. destruct vt_match. destruct t2; unfold is_address; simpl; auto.
          -- subst. unfold memory_address_correctness in *. simpl in *. remember (@eq_op (Ord.eqType _) w1 w2) as cond.
             destruct vt_match. subst t. unfold is_address.
             destruct t2; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond; destruct cond; simpl; convert_eq_op;
               try eapply (s'_mem_cor _ _ _ vt_eq0).
          -- subst. simpl. destruct t2; simpl; auto.
          -- unfold updm. rewrite setmE. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             rewrite <- Heqcond. destruct cond; try done. rewrite R2W. done.
          -- unfold updm. rewrite setmE. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             rewrite <- Heqcond. destruct cond; try done. rewrite vt_eq. simpl. done.
          -- subst s1. simpl in *. rewrite R1W in Heqa12. simplify_some. simpl.
             simpl. remember (@eq_op (Ord.eqType _) r2 r1) as cond. destruct cond.
             ++ assert (r_eq: r2 = r1) by (clear - Heqcond; eq_op_to_eq). rewrite r_eq. do 2 rewrite setmxx.
                simpl in *. rewrite setmE in Heqa13. simpl in *. rewrite <- Heqcond in Heqa13. simplify_some. simpl.
                rewrite <- r_eq in R1W. rewrite R1W in R2W. simplify_some. subst. done.
             ++ simpl in *. rewrite setmE in Heqa13. simpl in *. rewrite <- Heqcond in Heqa13. rewrite R2W in Heqa13. simplify_some.
                simpl. done.
          -- subst. simpl. destruct vt_match; subst. done.
      + subst. pose proof (s_reg_cor _ _ RW) as cor_RW. simpl in cor_RW.
        assert (Hyp: t1 = InternalJump \/ exists n, t1 = Ret n).
        { clear - Heqa7; repeat (unfold check_ret in *; (unfold_all || unfold_match)); eauto. }
        remember t1 as t1'.
        destruct t1; subst t1'; try (destruct Hyp as [?|Hyp]; try destruct Hyp; done);
          simpl in cor_RW; destruct cor_RW as [? [? [? ?]]]; eauto.
      + repeat
          (let va := fresh "va" in
           let ta := fresh "ta" in
           match goal with
             a: atom _ value_tag |- _ => destruct a as [va ta]
           end).
        simpl in *.
        repeat
          (match goal with
             H: Some _ = getm (setm _ _ _) _ |- _ =>
               repeat (rewrite setmE in H; unfold as_word in H; simpl in H)
           end).
        repeat
          (match goal with
             H: Some _ = match (eq_op (_ (_ ((_ (_ ?a _)) _ _))) _) with _ => _ end,
               H' : Some _ = getm _ (as_word (_ ?a))
             |- _ => idtac a; unfold as_word in H'; rewrite ST in H; simpl in H', H; rewrite <- H' in H
           end).
        rewrite ST RW in Heqa21. simplify_some. subst va19 ta19.
        deduce_equality RW.
        deduce_equality (esym Heqa9).
        deduce_equality (esym Heqa6).
        deduce_equality (esym Heqa11).
        deduce_equality (esym Heqa12).
        deduce_equality (esym Heqa13).
        deduce_equality (esym Heqa14).
        deduce_equality (esym Heqa15).
        deduce_equality (esym Heqa16).
        deduce_equality (esym Heqa17).
        deduce_equality (esym Heqa18).
        eexists. exists M.
        split.
        * eapply (plus_left _ [::]); try eapply step_jump. eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- unfold reg_clear_list, reg_list. simpl. unfold as_word. subst. simpl.
             repeat
               (match goal with
                | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
                end). trivial.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match.
             subst s1 s3. simpl in *.
             inversion vt_match. subst t. oapp_False. destruct res as [resv rest]. subst v0.
             match type of (res_eq) with (_ = Some (_@?t)) => assert (res_col: color t = i0) by (inversion Heqa2; done) end.
             match type of (res_eq) with (_ = Some (_@?t)) => assert (res_code': LRC.is_code t) by (simpl; done) end.
             assert (rel: is_relevant_comp Left i0). { clear - side_eq. unfold side_of in *. unfold_match' side_eq. }
             pose proof ((fst (code_left w resv _ off _ rel eq_off res_code' res_col))) as impl.
             simpl in impl. pose proof (impl (res_eq)) as [? [? pc3'eq]]. simpl.
             simpl in HeqH1. rewrite eq_off in HeqH1. simplify_some. rewrite pc3'eq. simpl.
             destruct rest. simpl in res_col. rewrite res_col. rewrite eq_refl. simpl.
             unfold updm. simpl in pc3'eq. unfold as_word.
             try rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. try rewrite ST. rewrite eq_refl. simpl.
             (*automatically rewrite regs3 registers*)
             repeat
             (repeat
                (match goal with
                 | H: getm _ ?w = _  |- context[getm _ ?w] => rewrite H; simpl
                 end);
              (*automatically transforms setm in if (_ == _) then _ else _*)
              repeat rewrite setmE; simpl;
              (*destruct the (_ == _) condition *)
              try
                (let cond := fresh "cond" in
                 match goal with
                 | |- context[@eq_op ?t ?a ?r] =>
                     remember (@eq_op t a r) as cond; destruct cond;
                     [convert_eq_op; simpl in *|]; simpl
                 end)).
             11: trivial.
             all: repeat (rewrite setmxx || (rewrite (setmC _ (_@InternalJump)); [|done]) ).
             all: (match (type of vt_eq) with
                   | ?ls = ?rs =>
                       revert vt_eq;
                       (match goal with
                          Heq: ls = Some (?a) |- _ =>
                            intro vt_eq; rewrite Heq in vt_eq; simplify_some; subst; done
                        end)
                   end).
          -- eapply star_refl.
          -- done.
        * destruct vt_match. oapp_False. subst. simpl in *.
          rewrite eq_off in HeqH2. simplify_some.
          repeat match goal with
            H: getm regs3 ?r = Some ?v |- context[setm regs3 ?r ?v] => idtac H; rewrite (setmI H)
          end.
          (match goal with
             |- (_ _ _ ?s _) /\ _ => assert(eq_tmp: regs s = reg); [|simpl in eq_tmp; rewrite eq_tmp; clear eq_tmp]
           end).            
          { simpl.
            rewrite (setmI RW). unfold as_word. simpl.
            repeat
            ((* this instruction branches on the value of r *)
              (match goal with
               | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                   unfold_match' H; simplify_some; subst; convert_eq_op; simpl in *
               end);
              (* if r is a value that is being rewriten, this deduces new equalities *)
              try (match (type of vt_eq) with
                   | ?ls = ?rs =>
                       (match goal with
                          Heq: ls = Some (?a), Hmatch: (data_match _ _ _ _ ?a)  |- _ =>
                            rewrite vt_eq in Heq; simplify_some; inversion Hmatch; subst; rewrite (setmI RW)
                        end)
                   end);
              repeat (simplify_some; subst);
              (* shows that the setm are not changing the values *)
              repeat
                (match goal with
                   H: Some ?v = getm reg ?r |- context[setm reg ?r ?v] => rewrite (setmI (esym H))
                 end);
              try trivial).
          }
          unfold color_of in tag_pc3, tag_pc1. simpl in tag_pc3, tag_pc1. inversion tag_pc1. subst n1.
          eapply preserves_equiv_left_pc_incr with (pc1' := (w)) (tpc1':=pc3_tag)
                                                   (pc3' := (addw w (as_word off))) (tpc3':=(pc3_tag)); subst pc3_tag.
          eauto. auto. auto.
          all: simpl; try trivial.
          all: unfold updm.
          all: try done.
          -- subst. simpl. eapply same_pc_normal.
             subst. simpl. eauto.
             unfold color_of. subst. simpl in *. eauto.
             subst. simpl. trivial. 
      + remember pc' as w'. unfold pc' in Heqw'.
        match (type of Heqw') with
          _ = (_ _ (match ?c as _ with _ => _ end)) => remember c as cond
        end. destruct cond; subst w'; try (rewrite Heqi'; eauto).
        subst. unfold_match' Heqa5. unfold is_code in Heqa3. unfold_match' Heqa3. pose proof (bnz_s1 _ _ PC) as H.
        simpl in H. simpl in *. rewrite <- Heqa1 in H. simpl in *. rewrite H0 in H. destruct H as [? [? ?]]; auto. eauto.
      + inversion Heqa2.
        deduce_equality RW.
        destruct res as [resv rest]. simpl in H1.
        subst rest.
        destruct vt_match as [? match_t]. subst t1. destruct t; unfold is_other in *; try congruence. subst w.
        remember (@eq_op (mword_eqType _) v0 zerow) as cond.
        remember (pc3_val + (if cond then 1 else swcast n0))%w as pc3'.
        rewrite ST eq_s3 in pc_s1_s3, code_left. simpl in *.
        unfold side_of in *. unfold_match' side_eq. simpl in *.
        (*
        assert (pceq': pc3' = (pc' + (as_word off))%w).
        { subst pc3' pc3_val pc'. rewrite <- Heqcond. rewrite <- addwA. rewrite (addwC (as_word off) _).
          rewrite addwA. trivial. }
        *)
        deduce_equality PC. rewrite eq_s3 in bnz_s3.
        pose proof (bnz_s3 _ _ vt_eq0) as H. simpl in H. eapply modusponens; [apply H; auto|]. clear H.
        unfold decode_match in *. revert vt_match. decode_instr_eq. intro. subst v1.
        decode_instr_eq. intros [v' [v'eq v'code]]. rewrite eq_s3 in end_s3.
        pose proof (end_s3 _ _ vt_eq0 t_code). revert H. decode_instr_eq. intro H. destruct H; try contradiction.
        destruct H as [v'' [v''eq v''code]].
        assert (next_pc_eq : mem3 pc3' = Some (if cond then v'' else v')).
        { subst pc3'. destruct cond; simpl; auto. }
        assert (pc'_eq: pc3' = (pc' + as_word off)%w).
        {subst. simpl in *. subst. unfold pc'. subst.
         rewrite <- addwA. rewrite (addwC (as_word _) (if _ then _ else _)).
         rewrite addwA. reflexivity. }
        deduce_equality res_eq. rewrite next_pc_eq in vt_eq1. simplify_some.
        eexists. exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_bnz. eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match. rewrite <- Heqcond. rewrite <- Heqpc3'. rewrite eq_s3 next_pc_eq. simpl.
             unfold check_belong. rewrite H1. simpl. rewrite eq_refl. simpl.
             unfold updm. subst. rewrite vt_eq. simpl. 
             try rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. try rewrite ST. rewrite eq_refl. simpl.
             reflexivity.
          -- destruct cond; eapply star_refl.
          -- done.
        * eapply preserves_equiv_left_reg_write with (r := r) (v := v0@Other) (v' := (v0@Other)).
          eapply preserves_equiv_left_pc_incr with (pc1' := pc') (tpc1' := taga (pc s1))
                                                   (pc3' := pc3') (tpc3' := taga (pc s3)); auto. eauto.
          all: simpl; try trivial.
          all: unfold updm.
          all: try done.
          -- subst. simpl. eapply same_pc_normal.
             simpl. eauto.
             unfold color_of. simpl. eauto.
             simpl. unfold pc'. trivial.
          -- subst. simpl in *. rewrite RW. simpl. trivial.
          -- rewrite vt_eq. simpl. trivial.
          -- subst. simpl in *. rewrite <- Heqa9 in RW. simplify_some. trivial.
          -- subst. simpl in *. trivial.
      + (*normal JAL*)
        (* we start by proving that pc' points to code *)
        unfold pc' in *. rewrite ST in bnz_s1, PC, alloc_mem_s1. pose proof (bnz_s1 _ _ PC) as JALcond.
        revert JALcond. decode_instr_eq. intro JALcond.
        destruct JALcond as [[x [next_pc_content' next_pc_code]] | imm_alloc_eq ]; auto.
        2: { exfalso. subst imm. inversion Heqa2. destruct a9 as [va ta]. simpl in *. subst ta.
             assert ((@swcast _ (word_size mt) (@word_of_nat (imm_size mt) alloc_label)) = ((word_of_nat alloc_label))).
             { unfold swcast, word_of_nat. simpl.
               unfold alloc_label. rewrite div.modn_small. trivial. trivial. }
             rename Heqnext_pc_content into H'.
             rewrite H in H'. rewrite alloc_mem_s1 in H'. inversion H'. }
        rewrite <- Heqnext_pc_content in next_pc_content'. simplify_some. inversion Heqa2.
        (* unfolding of the modified registers and their value *)
        repeat
          (let va := fresh "va" in
           let ta := fresh "ta" in
           match goal with
             a: atom _ value_tag |- _ => destruct a as [va ta]
           end).
        simpl in *.
        repeat
          (match goal with
             H: Some _ = getm (setm _ _ _) _ |- _ =>
               repeat (rewrite setmE in H; unfold as_word in H; simpl in H)
           end). 
        simpl in *.
        deduce_equality (esym Heqa9).
        deduce_equality (esym Heqa6).
        deduce_equality (esym Heqa11).
        deduce_equality (esym Heqa12).
        deduce_equality (esym Heqa13).
        deduce_equality (esym Heqa14).
        deduce_equality (esym Heqa15).
        deduce_equality (esym Heqa16).
        deduce_equality (esym Heqa17).
        deduce_equality (esym Heqa18).
        deduce_equality OLD.
        subst. unfold side_of in *. unfold_match' side_eq. simpl in *.
        deduce_equality PC.
        (* quick proof that v10 (s3) is a JAL offseted from i (s1) *)
        unfold decode_match in *. revert vt_match10. decode_instr_eq.
        intro v10_prop. unfold_all; try (subst; rewrite <- Heqa1 in Heqa4; inversion Heqa4; done).
        match (type of v10_prop) with
          match (?cond) with _ => _ end =>
            destruct cond eqn:X; try (subst; rewrite <- Heqa1 in Heqa4; simplify_some; rewrite H0 in X; inversion X; done)
        end.
        match (type of v10_prop) with | match ?cond with _ => _ end => destruct cond eqn: condeq end.
        { destruct (orb_prop _ _ condeq) as [eqalloc | eqalloc]; pose proof (esym eqalloc); convert_eq_op; subst;
          unfold alloc_empty in *; rewrite alloc_mem_s1 in Heqnext_pc_content; inversion Heqnext_pc_content. }
        assert (pc_eq_imm: (@swcast _ (word_size mt) i1) = addw (swcast imm) (as_word off)).
        { subst. admit. } (* probably doable with slight lemma/hypothesis on off *)
        destruct x as [vx tx].
        destruct ((fst (code_left _ vx tx off _ comp_in eq_off next_pc_code (esym (congr1 color H1)))) (esym Heqnext_pc_content))
        as [d [dmatch deq]].
        simpl in *.
        repeat ((match goal with
             H : Some _ = getm reg (as_word (_ ?a)), H': Some _ = getm reg (_ (_ ((_ (_ ?a _) _ _)))) |- _ =>
               idtac a; unfold as_word in H; simpl in H; rewrite <- H in H'; simplify_some; subst
          end)).
        eexists. exists M.
        split.
        * eapply (plus_left _ [::]); try eapply step_jal. eauto.
          -- exact vt_eq10.
          -- simpl. decode_instr_eq.
          -- exact vt_eq9.
          -- unfold reg_clear_list, reg_list. simpl. unfold as_word. subst. simpl.
             repeat
               (match goal with
                | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
                end). trivial.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match. simpl in *. rewrite pc_eq_imm deq. simpl. rewrite eq_refl. simpl.
             unfold updm.
             repeat((repeat
                (match goal with
                 | H: getm _ ?w = _  |- context[getm _ ?w] => rewrite H; simpl
                 end)); repeat rewrite setmE; simpl; try trivial).
          -- eapply star_refl.
          -- done.
        * simpl in *.
          repeat rewrite (setmC _ (_@InternalJump) _). all: try (simpl; done).
          repeat
            (match goal with
             | H: Some ?v = getm ?m ?r |- context[setm ?m ?r ?v] => rewrite (setmI (esym H))
             | H: getm ?m ?r = Some ?v |- context[setm ?m ?r ?v] => rewrite (setmI H)
             end).
          unfold color_of in tag_pc1. simpl in tag_pc1. inversion tag_pc1. subst n1.
          eapply preserves_equiv_left_reg_write with (r := ra) (v := (pc0 + 1)%w @InternalJump) (
                                                       v' := ((pc0 + as_word off + 1)%w @InternalJump)).
          eapply preserves_equiv_left_pc_incr with (pc1' := (swcast imm)) (tpc1':= Level n i0)
                                                   (pc3' := (swcast imm + as_word off)%w) (tpc3':= Level n i0).
          eauto. auto. auto.
          all: simpl; try trivial.
          all: unfold updm.
          all: try done.
          -- subst. simpl. eapply same_pc_normal.
             simpl. eauto.
             unfold color_of. simpl. eauto. simpl. trivial.
          -- pose proof (end_s3 _ _ vt_eq10). simpl in H. revert H. decode_instr_eq.
             intro H. destruct H; auto; try contradiction.
             split; auto. simpl. rewrite eq_off. simpl.
             rewrite <- addwA. rewrite (addwC (as_word _) onew). rewrite addwA. trivial.
          -- rewrite Heqi'. eexists. split; eauto.
          -- pose proof (end_s3 _ _ vt_eq10). simpl in H. revert H. decode_instr_eq.
             intro H. destruct H; auto; try contradiction.
          -- rewrite OLD. simpl. trivial.
          -- rewrite vt_eq9. simpl. trivial.
      + (*JAL to alloc*)
        unfold pc' in *. rewrite ST in bnz_s1. pose proof (bnz_s1 _ _ PC) as JALcond. simpl in JALcond.
        (match goal with
         | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
           => simpl; rewrite <- op in JALcond; simpl in JALcond; rewrite inst in JALcond
         end). destruct JALcond as [[? [tmp_eq next_pc_code]] | imm_alloc_eq ]; auto.
        { exfalso. rewrite <- Heqnext_pc_content in tmp_eq. inversion tmp_eq. }
        inversion Heqa2.
        (* unfolding of the modified registers and their value *)
        repeat
          (let va := fresh "va" in
           let ta := fresh "ta" in
           match goal with
             a: atom _ value_tag |- _ => destruct a as [va ta]
           end).
        simpl in *.
        repeat
          (match goal with
             H: Some _ = getm (setm _ _ _) _ |- _ =>
               repeat (rewrite setmE in H; unfold as_word in H; simpl in H)
           end).
        simpl in *.
        repeat ((match goal with
             H : Some _ = getm reg (as_word (_ ?a)), H': Some _ = getm reg (_ (_ ((_ (_ ?a _) _ _)))) |- _ =>
               idtac a; unfold as_word in H; simpl in H; rewrite <- H in H'; simplify_some; subst
          end)).
        deduce_equality (esym Heqa9).
        deduce_equality (esym Heqa6).
        deduce_equality (esym Heqa11).
        deduce_equality (esym Heqa12).
        deduce_equality (esym Heqa13).
        deduce_equality (esym Heqa14).
        deduce_equality (esym Heqa15).
        deduce_equality (esym Heqa16).
        deduce_equality (esym Heqa17).
        deduce_equality (esym Heqa18).
        deduce_equality OLD.
        subst. unfold side_of in *. unfold_match' side_eq. simpl in *.
        deduce_equality PC.
        (* quick proof that v10 (s3) is a JAL offseted from i (s1) *)
        unfold decode_match in *. revert vt_match10. decode_instr_eq. rewrite eq_refl. simpl.
        intro v10_prop. unfold_all; try (subst; rewrite <- Heqa1 in Heqa4; inversion Heqa4; done).
        match (type of v10_prop) with
          match (?cond) with _ => _ end =>
            destruct cond eqn:X; try (subst; rewrite <- Heqa1 in Heqa4; simplify_some; rewrite H0 in X; inversion X; done)
        end.
        subst i1. simpl in *.
        repeat ((match goal with
             H : Some _ = getm reg (as_word (_ ?a)), H': Some _ = getm reg (_ (_ ((_ (_ ?a _) _ _)))) |- _ =>
               idtac a; unfold as_word in H; simpl in H; rewrite <- H in H'; simplify_some; subst
          end)).
        eexists. exists M.
        split.
        * eapply (plus_left _ [::]); try eapply step_jal. eauto.
          -- exact vt_eq10.
          -- simpl. decode_instr_eq.
          -- exact vt_eq9.
          -- unfold reg_clear_list, reg_list. simpl. unfold as_word. subst. simpl.
             repeat
               (match goal with
                | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
                end). trivial.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match. simpl in *. rewrite alloc_mem_s3. simpl.
             unfold updm, color_of. simpl. rewrite eq_refl. simpl.
             (repeat
                (*automatically rewrite regs3 registers*)
                ((repeat
                   (match goal with
                    | H: _ ?w = _  |- context[isSome(_ ?w)] =>rewrite H; simpl
                    end);
                 (*automatically transforms setm in if (_ == _) then _ else _*)
                 repeat rewrite setmE; simpl
                ); try trivial)).
          -- eapply star_refl.
          -- done.
        * simpl in *.
          repeat rewrite (setmC _ (_@InternalJump) _). all: simpl. all: try tauto.
          repeat
            (match goal with
             | H: Some ?v = getm ?m ?r |- context[setm ?m ?r ?v] => rewrite (setmI (esym H))
             | H: getm ?m ?r = Some ?v |- context[setm ?m ?r ?v] => rewrite (setmI H)
             end).
          unfold color_of in tag_pc1. simpl in tag_pc1. inversion tag_pc1. subst n1.
          eapply preserves_equiv_left_reg_write with (r := ra) (v := (pc0 + 1)%w @InternalJump) (
                                                       v' := ((pc0 + as_word off + 1)%w @InternalJump)).
          eapply preserves_equiv_left_pc_incr with (pc1' := (word_of_nat alloc_label)) (tpc1':= Level n i0)
                                                   (pc3' := (word_of_nat alloc_label)%w) (tpc3':= Level n i0).
          eauto. auto. auto.
          all: simpl; try trivial.
          all: unfold updm.
          -- subst. simpl. eapply same_pc_alloc; simpl. trivial. exact alloc_mem_s1.
          -- split;auto. simpl. rewrite eq_off. simpl. rewrite <- addwA. rewrite (addwC _ onew).
             rewrite addwA. trivial.
          -- rewrite Heqi'. eexists. split; eauto.
          -- pose proof (end_s3 _ _ vt_eq10). simpl in H. revert H. decode_instr_eq.
             intro H. destruct H; auto; try contradiction.
          -- rewrite OLD. simpl. trivial.
          -- rewrite vt_eq9. simpl. trivial.
      + destruct pc_s1_s3 as [s1 s3 pc_s1_s3 eq_none|s1 s3 ? ? eq_some eq_off pc_s1_s3].
        2: { exfalso. rewrite ST in eq_some. unfold color_of in eq_some. simpl in eq_some. rewrite PC in eq_some. inversion eq_some. }
        unfold run_syscall in *.
        unfold evi in *. repeat unfold_bind. inversion CALL. subst s1'. simpl.
        simpl in Heqa0. unfold Instance.table, table in *. simpl in GETCALL.
        rewrite setmE in GETCALL. unfold_match' GETCALL. repeat simplify_some.
        assert (exists s3', alloc_fun s3 = Some s3') as [s3' s3'_eq].
        { unfold Symbolic.sem in *.
          unfold alloc_fun in *.
          do 2 unfold_all || unfold_match.
          unfold updm in Heqa1.
          repeat (unfold_all || unfold_match).
          unfold isSome in Heqa10.
          remember (regs s1 (as_word (ssrint.Posz 16))) as retval. simpl in *. rewrite <- Heqretval in Heqa9.
          destruct retval as [retval|]; try (inversion Heqa9; done).
          destruct a0 as [va ?]. unfold is_jump in *. destruct taga; inversion Heqa4.
          destruct ((snd (reg_match _ _)) (esym Heqa3)) as [b [bmatch beq]].
          destruct ((snd (reg_match _ _)) (esym Heqa5)) as [b' [b'match b'eq]].
          destruct ((snd (reg_match _ _)) (esym Heqretval)) as [b'' [b''match b''eq]].
          rewrite beq. simpl. destruct b as [bv bt]. destruct bmatch. subst bt. simpl.
          rewrite b'eq. simpl. unfold is_other in *. destruct a1, b'. destruct b'match. subst taga0.
          destruct taga; inversion Heqa6. simpl. (*
          destruct b as [bv bt]. destruct bmatch. subst bt. oapp_False.
          rename i0 into off. rename HeqH into eq_off.
          assert (rel: is_relevant_comp Left (color_of s1)). { clear - side_eq. unfold side_of in *. unfold_match' side_eq. }
          pose proof (s_reg_cor _ _ (esym Heqa3)) as H. simpl in H. destruct H as [d [deq dcode]]. destruct d as [vd td].
          pose proof ((fst (code_left va _ _ off _ rel (esym eq_off) dcode (Logic.eq_refl))) (deq)) as s3_deq.
          destruct s3_deq as [? [? s3_deq]].
          eexists.
          rewrite beq. simpl.
          simpl in *. rewrite <- H0 in s3_deq. rewrite s3_deq. simpl.
          rewrite b'eq. simpl.
          unfold is_other in *. destruct a2 as [a2v a2t]. destruct b' as [b'v b't].
          destruct a2t; try (inversion Heqa7; done). destruct b'match. subst b'v b't. simpl.*)
          subst s1 s3. simpl in *. rewrite <- comp_num. destruct pc3_tag. simpl.
          inversion tag_pc1. inversion tag_pc3. subst n1 n0 i i0.
          assert (domm_eq: (List.filter
                              (fun mw : word 32 =>
                                 andw mw (@component_memory_prefix mt (ssrint.Posz ((Nat.pow 2 nc) - 1)) nc) ==
                                   @component_memory_prefix mt (ssrint.Posz (1 + color)) nc) (domm mem0))
                           = (List.filter
                                (fun mw : word 32 =>
                                   andw mw (@component_memory_prefix mt (ssrint.Posz ((Nat.pow 2 nc) - 1)) nc) ==
                                     @component_memory_prefix mt (ssrint.Posz (1 + color)) nc) (domm mem3))). admit.
          simpl in *. rewrite <- domm_eq. subst vala0.
          rewrite <- Heqa7. rewrite <- Heqa10. simpl.
          rewrite <- Heqa1. simpl. unfold updm. rewrite b''eq. simpl. eauto. }
        exists s3'; exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_syscall; eauto.
          -- eapply (etrans _ (PC)).
          -- subst. simpl in *. rewrite <- pc_s1_s3. unfold Instance.table, table. convert_eq_op. subst. simpl.
             rewrite setmE. rewrite eq_refl. done.
          -- unfold run_syscall, evi. deduce_reg reg_match. rewrite s3'_eq. simpl. done.
          -- eapply star_refl.
          -- done.
        * eapply preserves_equiv_left_alloc_fun; eauto; done.
  Admitted.


  (*** Final Proofs ***)
      
  Theorem tsim_properties_match_states:
    @tsim_properties sem sem' sem'' (sd_traces det_sem) (sd_traces det_sem') (sd_traces det_sem'')
      (fun s1 s2 s3 => exists M, match_states M s1 s2 s3).
  Proof.
    eapply threeway_simulation_properties.
    - eapply match_initial_states.
    - eapply step_silent_strong1.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Corollary recomposition_blame:
    forall m,
      does_prefix sem   m ->
      does_prefix sem'  m ->
      does_prefix sem'' m.
  Proof.
    setoid_rewrite (does_prefix_equiv det_sem).
    setoid_rewrite (does_prefix_equiv det_sem').
    setoid_rewrite (does_prefix_equiv det_sem'').
    intros m dp_sem dp_sem'.
    pose proof tsim_properties_match_states as props.
    inversion dp_sem; subst; inversion dp_sem'; subst;
      try (match goal with | H : (forall s : Smallstep.state _, ~ Smallstep.initial_state _ s) |- _ =>
                               exfalso; eapply H; simpl; unfold initial_state2; unfold initial_state1; eauto end);
      remember (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')) as s3;
      try (assert (match_s3: exists M, match_states M s s0 s3) by 
          (( match goal with | H : (Smallstep.initial_state sem _), H' : (Smallstep.initial_state sem' _) |- _ =>
                                 rename H into init_sem; rename H' into init_sem' end);
           destruct props as [a]; destruct (a _ _ init_sem init_sem') as [s3' [init match_init]];
           simpl in init; unfold initial_state3 in init;
           rewrite <- init in Heqs3; subst; try done));
      try ((match goal with | H : (Star sem' _ _ _) |- _ => rename H into star end));
      ((destruct (tsimulation_star props H0 star s3 match_s3) as [s3' [star_sem'' ?]]);
       assert (init: Smallstep.initial_state sem'' s3) by done).
    - apply (does_FTbc (init) star_sem'').
    - apply (does_FGoes_wrong (init) star_sem'').
      + admit.
      + admit. (* we should use properties of match_states and final_states here. *)
    - apply (does_FTerminates (init) star_sem'').
      admit. (* we should use properties of match_states and final_states here. *)
  Admitted.

  Corollary recomposition_blame':
    forall m,
      does_prefix sem   (FGoes_wrong m) ->
      does_prefix sem'  (FTbc m) ->
      Common.Blame.undef_in m ip ->
      does_prefix sem'' (FGoes_wrong m).
  Proof.
    setoid_rewrite (does_prefix_equiv det_sem).
    setoid_rewrite (does_prefix_equiv det_sem').
    setoid_rewrite (does_prefix_equiv det_sem'').
    intros m dp_sem dp_sem' undef_m_ip.
    pose proof tsim_properties_match_states as props.
    inversion dp_sem; inversion dp_sem';
      try (match goal with | H : (forall s : Smallstep.state _, ~ Smallstep.initial_state _ s) |- _ =>
                               exfalso; eapply H; simpl; unfold initial_state2; unfold initial_state1; eauto end).
    remember (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')) as s3.
    assert (match_s3: exists M, match_states M s s0 s3).
    { destruct props as [a]. destruct (a _ _ H0 H5) as [s3' [init match_init]].
      simpl in init. unfold initial_state3 in init.
      rewrite <- init in Heqs3. subst. done. }
    destruct (tsimulation_star props H1 H6 s3 match_s3) as [s3' [star_sem'' ?]].
    econstructor.
    - simpl; unfold initial_state3; eauto.
    - eauto.
    - admit.
    - admit.
  Admitted.

End Recomposition.

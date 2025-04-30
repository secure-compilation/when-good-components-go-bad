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

Definition find_procedure p comp proc :=
  Exists (fun '(_, tag) =>
            match (entry tag) with
            | None => False
            | Some (proc', lc) => (proc = proc') /\ (In comp lc)
            end) (code p).

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
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.

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
  
  Definition color_of: state -> option Component.id :=
    fun '(Symbolic.State mem regs (Types.Atom pc _) _ _) =>
      match (mem pc) with
      | None => None
      | Some (Types.Atom _ tag) => Some (color tag)
      end.

  Definition color_of': state -> option Component.id :=
    fun '(Symbolic.State mem regs (Types.Atom pc _) _ _) =>
      match (mem pc) with
      | None => None
      | Some (Types.Atom _ tag) => if (is_code tag) then Some (color tag) else None
      end.
  
  Definition allowed_UB: state -> Prop :=
    fun s => Option.apply (fun comp => (comp \in (domm ic)):Prop) False (color_of s).

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

    Definition side_of' c: side :=
      if c \in domm ip then Left else Right.
    
    Definition side_of (s: state): option side :=
      do! c <- color_of s; Some (side_of' c).

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
                  do! p_s2 <- p0 prog comp;
                  Some (encode_int (Z.of_nat p_s3 - Z.of_nat p_s2)))
        (domm ic).

    Definition stack: Type := seq (stack_value * stack_value * stack_value * Component.id).
    Definition metadata := stack.

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
        points_to_comp_code' i (side_of' c) (mem) (Types.vala v) c
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
        (PTS_CODE1: points_to_comp_code' Right (side_of' C) m1 v1 C)
        (PTS_COD22: points_to_comp_code m2 v2 C)
        (PTS_CODE3: points_to_comp_code m3 v3 C)
        (VALA_OFF: v3 = addw v1 (as_word off))
        (WF_ST: wf_stack m1 m2 m3 n st),
        wf_stack m1 m2 m3 (n+1)
          ((Types.Atom v1 (Ret n), Types.Atom v2 (Ret n), Types.Atom v3 (Ret n), C) :: st)
    | wf_stack_cons_right: forall n st v1 v2 v3 C off,
      forall (SIDE: is_relevant_comp Right C)
        (OFF_C: get_offset Right C = Some off)
        (PTS_CODE1: points_to_comp_code' Right (side_of' C) m1 v1 C)
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
            | InternalJump => Option.apply (fun off => v1 = addw v2 (as_word off)) False (get_offset i comp)
            | Ret _ =>
                match i with
                | Left  => exists sv', In (d, sv', d', comp) (m)
                | Right => exists sv', In (sv', d, d', comp) (m)
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
      forall c w d,
        color_of s = Some c ->
        ((regs s' w) = Some d -> exists d', data_match i c m d' d /\ (regs s  w) = Some d') /\
          ((regs s  w) = Some d -> exists d', data_match i c m d d' /\ (regs s' w) = Some d').
    
    Variant same_pc (i: side): state -> state -> Prop :=
      | same_pc_alloc: forall s s',
          vala (pc s) = vala (pc s') ->
          mem s (vala (pc s)) = None ->
          same_pc i s s'
      | same_pc_normal: forall s s' comp off,
          color_of s = Some comp ->
          get_offset i comp = Some off ->
          vala (pc s') = addw (Types.vala (pc s)) (as_word off) ->
          same_pc i s s'
    .

    Definition combined_codes (i: side) (m: metadata) (s: state) (s': state) : Prop :=
      forall w v off c,
        is_relevant_comp i c ->
        get_offset Left c = Some off ->
        is_code (Types.taga v) ->
        color (Types.taga v) = c ->
        ((mem s' (addw w (as_word off)) = Some v) <-> (mem s w = Some v)).

    Definition end_condition (s: state) : Prop :=
      forall w v,
        mem s w = Some v ->
        is_code (taga v) ->
        (match (decode_instr (vala v)) with Some (Jump _) | Some (Jal _) | Some Halt => True | _ => False end)
        \/ exists v', (mem s (addw w onew) = Some v' /\ is_code (taga v'))
    .
    
    Variant common_equiv: metadata -> state -> state -> state -> Prop :=
      common_equiv_def : forall m s1 s2 s3 n,
          taga (@pc _ lrc_tags _ s1) = Level n ->
          taga (@pc _ lrc_tags _ s2) = Level n ->
          taga (@pc _ lrc_tags _ s3) = Level n ->
          wf_stack (mem s1) (mem s2) (mem s3) n m ->
          end_condition s1 ->
          end_condition s2 ->
          end_condition s3 ->
          combined_codes Left  m s1 s3 ->
          combined_codes Right m s2 s3 ->
          common_equiv m s1 s2 s3
    .
    Variant strong_equiv (i: side): metadata -> state -> state -> Prop :=
      strong_equiv_def : forall m s s',
          well_formed_metadata i m (mem s) (mem s') ->
          same_pc i s s' ->
          color_of s = color_of s' ->
          side_of s' = Some i ->
          memory_match i m s s' ->
          registers_match i m s s' ->
          strong_equiv i m s s'
    .

    Variant weak_equiv (i: side): metadata -> state -> state -> Prop :=
      weak_equiv_def : forall m s s',
          well_formed_metadata i m (mem s) (mem s') ->
          color_of s = color_of s' ->
          side_of s' = Some (other_side i) ->
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
    | H: (true = (?a == ?b)) |- _ => assert (a = b) by eq_op_to_eq; subst a; clear H
    end.
    
  Ltac oapp_False :=
    let b := fresh in
    match goal with | H: oapp _ False ?v |- _ => remember v as b; destruct b; try contradiction; simpl in H; try subst b end.

  Ltac resolve_register s s' reg_match (*: registers_match i M s s' *) NEXT color_s r :=
    remember (regs s r) as rv_tmp eqn:Heqrv; simpl in *; try rewrite <- Heqrv in NEXT;
    destruct rv_tmp as [rv|]; simpl in *; try (inversion NEXT; done);
    try (destruct (reg_match _ r rv color_s) as [_ impl];
         destruct (impl (esym Heqrv)) as [d' [d'_match d'_eq]]; rewrite d'_eq; simpl; clear impl).

  
  Ltac resolve_memory s s' i mem_match (*: registers_match i M s s' *) NEXT w :=
    remember (mem s w) as wv_tmp eqn:Heqwv; simpl in *; rewrite <- Heqwv in NEXT;
    destruct wv_tmp as [wv|]; simpl in *; try (inversion NEXT; done);
    try (assert (not_code: ~ is_code (taga wv)) by shelve;
         assert (relevant_comp: is_relevant_comp i (color (taga wv))) by shelve;
         destruct (mem_match w wv not_code relevant_comp) as [_ impl];
         destruct (impl (esym Heqwv)) as [d'' [d''_match d''_eq]]; rewrite d''_eq; simpl; clear impl).
  
  Ltac unfold_match :=
    let a := fresh "a" in
    match goal with
    | H : (match ?cond as _ return _ with _ => _ end) = _  |- _ => try(remember cond as a; destruct a);
                                                                simpl in H; try (inversion H; done)
    | H : _ = (match ?cond as _ return _ with _ => _ end)  |- _ => try(remember cond as a; destruct a);
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
    end.

  (*** Equivalence preservation lemmas ***)
  
  Lemma preserves_equiv_left_pc_incr :
    forall s1 s2 s3 M s1' s3' pc1' pc3',
      strong_equiv Left M s1 s3
      /\ weak_equiv Right M s2 s3
      /\ common_equiv M s1 s2 s3 ->
      s1' = State _ _ (mem s1) (regs s1) (pc1') tt (comp_num s1) ->
      s3' = State _ _ (mem s3) (regs s3) (pc3') tt (comp_num s3) ->
      same_pc Left s1' s3' ->
      taga pc1' = taga (pc s1) ->
      taga pc3' = taga (pc s3) ->
      color_of s1 = color_of s1' ->
      color_of s3 = color_of s3' ->
      strong_equiv Left M s1' s3'
      /\ weak_equiv Right M s2 s3'
      /\ common_equiv M s1' s2 s3'.
  Proof.
    intros s1 s2 s3 M s1' s3' pc1' pc3' equiv eq_s1' eq_s3' pc1'_pc3' pc1_tag pc3_tag color_s1 color_s3.
    destruct equiv as [strong [weak common]].
    split; [|split].
    - destruct strong as [? ? ? wf_m pc_s1_s3  color_eq side_eq mem_match reg_match].
      econstructor; try (rewrite eq_s1' eq_s3'; simpl; auto; done); try congruence.
      + unfold side_of, side_of' in *. rewrite <- color_s3. done.
      + unfold registers_match in *. rewrite <- color_s1. rewrite eq_s1' eq_s3'. simpl. assumption.
    - destruct weak as [? ? ? wf_m color_eq side_s' mem_match].
      econstructor; try (rewrite eq_s3'; simpl; auto; done); try congruence.
      + unfold side_of, side_of' in *. rewrite <- color_s3. done.
    - destruct common as [? ? ? ? n tag_pc1 tag_pc2 tag_pc3 wfst end_s1 end_s2 end_s3 code_left code_right].
      eapply common_equiv_def with (n := n);
        try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; try done.
      + rewrite eq_s1'. rewrite pc1_tag. done.
      + rewrite eq_s3'. rewrite pc3_tag. done.
  Qed.

    
  Lemma preserves_equiv_left_mem_write:
    forall s1 s2 s3 M s1' s3' w v v' m1' m3',
      strong_equiv Left M s1 s3
      /\ weak_equiv Right M s2 s3
      /\ common_equiv M s1 s2 s3 ->
      data_match' Left M v v' ->
      (color (taga v)) = (color (taga v')) ->
      is_relevant_comp Left (color (taga v)) ->
      (forall v', (mem s1 w) = Some v' \/ (mem s3 w) = Some v' -> (color (taga v)) = (color (taga v'))) -> 
      (exists d, mem s3 w = Some d /\ not (is_code (taga d))) ->
      (exists d, mem s1 w = Some d /\ not (is_code (taga d))) ->
      not (is_code (taga v)) ->
      not (is_code (taga v')) ->
      updm (mem s1) w v = Some m1' ->
      updm (mem s3) w v' = Some m3' ->
      s1' = State _ _ m1' (regs s1) (pc s1) tt (comp_num s1) ->
      s3' = State _ _ m3' (regs s3) (pc s3) tt (comp_num s3) ->
      color_of s1 = color_of s1' ->
      color_of s3 = color_of s3' ->
      strong_equiv Left M s1' s3'
      /\ weak_equiv Right M s2 s3'
      /\ common_equiv M s1' s2 s3'.
  Proof.
    intros s1 s2 s3 M s1' s3' w v v' m1' m3' equiv v_match v_color v_relevant same_color no_code_w_s3 no_code_w_s1
      no_code_v no_code_v' eq_m1 eq_m3 eq_s1' eq_s3' color_s1 color_s3.
    destruct equiv as [strong [weak common]].
    pose proof (updm_set eq_m1). pose proof (updm_set eq_m3). subst m1' m3'.
    split; [|split].
    - destruct strong as [? ? ? wf_m pc_s1_s3  color_eq side_eq mem_match reg_match].
      econstructor; try (rewrite eq_s1' eq_s3'; simpl; auto; done); try congruence.
      + intros ? ? ? ? comp ? in_m veq off_eq. subst v0. unfold mem. rewrite eq_s1' eq_s3'. simpl.
        unfold points_to_comp_code, points_to_comp_code'. rewrite setmE. rewrite setmE. split; [|split].
        * remember (@eq_op (Ord.eqType _) (Types.vala v1) w) as cond. destruct cond.
          -- assert (eq: Types.vala v1 = w) by eq_op_to_eq.
            pose proof (wf_m _ _ _ v1 _ off in_m) as conj. simpl in conj.
            destruct (conj) as [points_s [points_s' off_cond]]; auto.
            unfold points_to_comp_code' in points_s. rewrite eq in points_s. simpl.
            oapp_False. destruct points_s as [comp_eq disj].
            rewrite (same_color a); auto. split; auto. destruct disj as [[? ?] | ?] ; inversion H.
            exfalso. destruct no_code_w_s1 as [d [d_eq d_nocode]]. rewrite d_eq in HeqH. simplify_some. done.
          -- eapply wf_m; eauto.
        * remember (@eq_op (Ord.eqType _) (Types.vala v3) w) as cond. destruct cond.
          -- assert (eq: Types.vala v3 = w) by eq_op_to_eq.
            pose proof (wf_m _ _ _ v1 _ off in_m) as conj. simpl in conj.
            destruct (conj) as [points_s [points_s' off_cond]]; auto.
            unfold points_to_comp_code in points_s'. simpl.
            oapp_False. destruct points_s' as [comp_eq code]. rewrite <- v_color.
            rewrite (same_color a); auto. split; auto.
            exfalso. destruct no_code_w_s3 as [d [d_eq d_nocode]]. rewrite eq d_eq in HeqH. simplify_some. done.
            right. rewrite <- eq. done.
          -- eapply wf_m; eauto.
        * intro comp_in_ip. eapply (wf_m _ _ _ _ _ _ in_m); auto.
      + destruct common as [? ? ? ? wfst end_s1 end_s2 end_s3 code_left code_right].
        destruct pc_s1_s3 as [? ? ? eq_none|? ? ? ? eq_comp eq_off pc_s1_s3].
        * eapply same_pc_alloc; try rewrite eq_s1'; try rewrite eq_s3'; simpl; auto.
          rewrite setmE.
          remember (@eq_op (Ord.eqType _) (vala (pc s)) w) as cond. simpl in *. rewrite <- Heqcond.
          destruct cond; simpl; auto.
          exfalso. assert (eqw: vala (pc s) = w) by eq_op_to_eq. subst w.
          destruct no_code_w_s1 as [d [d_eq d_nocode]]. rewrite d_eq in eq_none. done.
        * eapply same_pc_normal; eauto. rewrite <- color_s1. auto.
        rewrite eq_s1' eq_s3'. simpl. done.
      + unfold side_of in *. rewrite <- color_s3. done.
      + unfold memory_match in *. rewrite eq_s1' eq_s3'. simpl.
        intros. 
        rewrite setmE. rewrite setmE.
        remember (@eq_op (Ord.eqType _) w0 w) as cond. destruct cond.
        * split; intro eq; inv eq; eexists; split; eauto.
        * apply mem_match; auto.
      + unfold registers_match in *. rewrite <- color_s1. rewrite eq_s1' eq_s3'. simpl. done.
    - destruct weak as [? ? ? wf_m color_eq side_s' mem_match].
      econstructor.
      + intros ? ? ? ? comp ? in_m veq off_eq. subst v0. rewrite eq_s3'. simpl.
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
            exfalso. destruct no_code_w_s3 as [d [d_eq d_nocode]]. rewrite eq d_eq in HeqH. simplify_some. done.
            right. rewrite <- eq. done.
          -- eapply wf_m; eauto.
        * intro comp_in_ip. eapply (wf_m _ _ _ _ _ _ in_m); auto.
      + rewrite <- color_s3. done.
      + unfold side_of in *. rewrite <- color_s3. done.
      + unfold memory_match in *. rewrite eq_s3'. simpl.
        intros.
        rewrite setmE.
        remember (@eq_op (Ord.eqType _) w0 w) as cond. destruct cond.
        * assert (eq_w: w0 = w) by eq_op_to_eq.
          subst. simpl in mem_match. split; intro eq; inv eq; exfalso.
          -- remember (mem s' w) as v_opt. destruct v_opt as [d'|].
             ++ assert (color (taga d) = color (taga d')) by (rewrite <- v_color; eapply same_color; auto). simpl in v_relevant.
                { eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
                  inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. rewrite <- v_color. auto. }
             ++ simpl in v_relevant. 
                { eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
                  inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. rewrite <- v_color. auto. }
          -- pose proof (mem_match w d H H0) as [_ d_impl].
             destruct (d_impl H2) as [d' [d_d'_match eq_d']].
             assert (d'_color: color (taga v) = color (taga d')) by (eapply same_color; auto).
             rewrite d'_color in v_relevant. assert (d'_color_bis: (color (taga d') = color (taga d))).
             { destruct d, d'. simpl. unfold data_match' in d_d'_match. destruct d_d'_match. subst. done. }
             rewrite <- d'_color_bis in H0. simpl in *. 
             { eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
               inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. }
        * apply mem_match; auto.
    - destruct common as [? ? ? ? n tag_pc1 tag_pc2 tag_pc3 wfst end_s1 end_s2 end_s3 code_left code_right]. 
      eapply common_equiv_def with (n := n); 
        try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; try done.
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
             ++ simpl in SIDE. unfold side_of' in side_of_C. inversion SIDE. rewrite H0 in side_of_C. inv side_of_C.
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
             left. split; auto. unfold side_of'. simpl in SIDE.
             assert (cond_eq: C \in domm ip = false).
             { assert (~ C \in domm ip). intro. 
               { eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
                 inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. }
               remember (C \in domm ip) as cond. destruct cond; auto. destruct H. done. } 
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
      + unfold end_condition in *. intros w0 v0 v0_eq v0_code.
        rewrite eq_s1' in v0_eq. simpl in v0_eq. rewrite setmE in v0_eq.
        remember (@eq_op (Ord.eqType _) w0 w) as cond. simpl in Heqcond. rewrite <- Heqcond in v0_eq. destruct cond.
        * simplify_some. contradiction.
        * destruct (end_s1 w0 v0 v0_eq v0_code); [left | right]; auto. destruct H as [v1 [v1_eq v1_code]].
          exists v1. rewrite eq_s1'. rewrite setmE.
          remember (@eq_op (Ord.eqType _) (addw w0 onew) w) as cond. destruct cond; try (split; done).
          exfalso. assert ((addw w0 onew) = w) by eq_op_to_eq. subst w.
          destruct no_code_w_s1 as [? [eq no_code]]. rewrite eq in v1_eq. simplify_some. done.
      + unfold end_condition in *. intros w0 v0 v0_eq v0_code.
        rewrite eq_s3' in v0_eq. simpl in v0_eq. rewrite setmE in v0_eq.
        remember (@eq_op (Ord.eqType _) w0 w) as cond. simpl in Heqcond. rewrite <- Heqcond in v0_eq. destruct cond.
        * simplify_some. contradiction.
        * destruct (end_s3 w0 v0 v0_eq v0_code); [left | right]; auto. destruct H as [v1 [v1_eq v1_code]].
          exists v1. rewrite eq_s3'. rewrite setmE.
          remember (@eq_op (Ord.eqType _) (addw w0 onew) w) as cond. destruct cond; try (split; done).
          exfalso. assert ((addw w0 onew) = w) by eq_op_to_eq. subst w.
          destruct no_code_w_s3 as [? [eq no_code]]. rewrite eq in v1_eq. simplify_some. done.
      + unfold combined_codes. intros w' d off comp relevant_comp offset v'_code v'_color.
        remember (addw w' (as_word off)) as w''. 
        remember (@eq_op (Ord.eqType _) w'' w) as cond. unfold mt, concrete_int_32_mt, word_size in Heqcond.
        destruct cond.
        * assert (eq_w: w'' = w) by eq_op_to_eq.
          split; intro eq; exfalso.
          -- rewrite eq_s3' in eq. simpl in eq.
             subst w. rewrite setmE in eq. rewrite <- Heqcond in eq.
             inv eq. tauto.
          -- subst w. remember (@eq_op (Ord.eqType _) w' w'') as cond'. unfold mt, concrete_int_32_mt, word_size in Heqcond'.
             destruct cond'.
             ** assert (eq_w: w' = w'') by eq_op_to_eq. subst w'.
                rewrite eq_s1' in eq. simpl in eq.
                rewrite setmE in eq. rewrite <- Heqcond in eq.
                inv eq. tauto.
             ** rewrite eq_s1' in eq. simpl in eq.
                rewrite setmE in eq. rewrite <- Heqcond' in eq.
                pose proof (code_left w' d off comp relevant_comp offset v'_code v'_color) as [_ impl].
                rewrite <- Heqw'' in impl.
                destruct no_code_w_s3 as [? [d_eq d_nocode]]. rewrite (impl eq) in d_eq. simplify_some. done.
        * rewrite eq_s3'. simpl. rewrite setmE. rewrite <- Heqcond.
          remember (@eq_op (Ord.eqType _) w' w) as cond'. unfold mt, concrete_int_32_mt, word_size in Heqcond'.
          destruct cond'.
          -- assert (eq_w: w' = w) by eq_op_to_eq. subst w. 
             rewrite eq_s1'. simpl. rewrite setmE. rewrite <- Heqcond'.
             pose proof (code_left w' d off comp relevant_comp offset v'_code v'_color) as equiv.
             rewrite <- Heqw'' in equiv. setoid_rewrite equiv.
             split; intro eq.
             ++ exfalso. 
                destruct no_code_w_s1 as [? [d_eq d_nocode]]. rewrite d_eq in eq. simplify_some. done.
             ++ inversion eq. subst d. exfalso. tauto.
          -- rewrite eq_s1'. simpl. rewrite setmE. rewrite <- Heqcond'. rewrite Heqw''.
             eapply code_left; eauto.
      + unfold combined_codes. intros w' d off comp relevant_comp offset v'_code v'_color.
        setoid_rewrite <- (code_right w' d off comp relevant_comp offset v'_code v'_color).
        remember (addw w' (as_word off)) as w''. 
        remember (@eq_op (Ord.eqType _) w'' w) as cond. unfold mt, concrete_int_32_mt, word_size in Heqcond.
        destruct cond.
        * assert (eq_w: w'' = w) by eq_op_to_eq.
          split; intro eq; exfalso.
          -- rewrite eq_s3' in eq. simpl in eq. subst w. rewrite setmE in eq. rewrite <- Heqcond in eq.
             inv eq. tauto.
          -- subst w. destruct no_code_w_s3 as [? [d_eq d_nocode]]. rewrite d_eq in eq. simplify_some. done.
        * rewrite eq_s3'. simpl. rewrite setmE. rewrite <- Heqcond. done. 
  Qed.

  Lemma preserves_equiv_left_reg_write :
    forall s1 s2 s3 M s1' s3' r v v' c r1' r3',
      strong_equiv Left M s1 s3
      /\ weak_equiv Right M s2 s3
      /\ common_equiv M s1 s2 s3 ->
      data_match Left c M v v' ->
      color_of s1 = Some c ->
      updm (regs s1) r v = Some r1' ->
      updm (regs s3) r v' = Some r3' ->
      s1' = State _ _ (mem s1) r1' (pc s1) tt (comp_num s1) ->
      s3' = State _ _ (mem s3) r3' (pc s3) tt (comp_num s3) ->
      color_of s1 = color_of s1' ->
      color_of s3 = color_of s3' ->
      strong_equiv Left M s1' s3'
      /\ weak_equiv Right M s2 s3'
      /\ common_equiv M s1' s2 s3'.
  Proof.
    intros s1 s2 s3 M s1' s3' r v v' comp r1' r3' equiv v_match comp_color eq_r1 eq_r3 eq_s1' eq_s3' color_s1 color_s3.
    destruct equiv as [strong [weak common]].
    split; [|split].
    - destruct strong as [? ? ? wf_m pc_s1_s3  color_eq side_eq mem_match reg_match].
      econstructor; try (rewrite eq_s1' eq_s3'; simpl; auto; done); try congruence.
      + destruct common as [? ? ? ? wfst end_s1 end_s2 end_s3 code_left code_right].
        destruct pc_s1_s3 as [? ? ? eq_none|? ? ? ? eq_comp eq_off pc_s1_s3].
        * eapply same_pc_alloc; try rewrite eq_s1'; try rewrite eq_s3'; auto.
        * eapply same_pc_normal; eauto. rewrite <- color_s1. auto.
          rewrite eq_s1' eq_s3'. simpl. done.
      + unfold side_of in *. rewrite <- color_s3. done.
      + unfold registers_match in *. rewrite eq_s1' eq_s3'. simpl. 
        intros. assert (c0 = comp).
        { unfold color_of in comp_color. destruct s. simpl in *. rewrite H in comp_color. congruence. } subst c0.
        pose proof (updm_set eq_r1). pose proof (updm_set eq_r3). subst r1' r3'.
        rewrite setmE. rewrite setmE.
        remember (@eq_op (Ord.eqType _) w r) as cond. destruct cond.
        *  split; intro eq; inv eq; eauto.
        * apply reg_match; auto.
    - destruct weak as [? ? ? wf_m color_eq side_s' mem_match].
      econstructor; try (rewrite eq_s3'; simpl; auto; done); try congruence.
      unfold side_of in *. rewrite <- color_s3. done.
    - destruct common as [? ? ? ? n tag_pc1 tag_pc2 tag_pc3 wfst end_s1 end_s2 end_s3 code_left code_right]. 
      eapply common_equiv_def with (n := n); 
        try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; try done.
  Qed.

  
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
    - unfold combined_codes. intros. admit.
    - unfold combined_codes. intros. admit.
    - unfold well_formed_metadata. intros. inv H.
    - assert (color_eq: color_of s1 = Some 0).
      { unfold initial_state in init1. simpl in init1. destruct s1. inv init1.
        unfold color_of. subst.
        pose proof (initial_memory_domm (unionm (prog_buffers p) (prog_buffers c))).
        remember (initial_memory (unionm (prog_buffers p) (prog_buffers c))) as im.
        rewrite unionmE.
        assert (eq: (encode_code (code p ++ code c) (size im) (word_of_nat (size im))) = None).
        { setoid_rewrite (rwP dommPn). rewrite encode_code_domm. unfold mt.
          remember (size (code p ++ code c)) as n. (* setoid_rewrite <- (rwP memPn). simpl.
          intros x x_in. clear -x_in.
          induction n.
          - simpl in *. rewrite <- fset0E in *. rewrite in_fset0 in x_in. done. *) admit. }
        admit.
      }      
  Admitted.

  
  Ltac deduct_color_eq :=
    unfold color_of; subst; simpl;
    repeat
      match goal with
      | |- Some (_ ?t) = _ => subst t; simpl
      | |- _ = Some (_ ?t) => subst t; simpl
      | |- match (setm _ _ _) with _ => _ end = _ => rewrite setmE; goal_match_bind_step
      | |- _ = match (setm _ _ _) with _ => _ end => rewrite setmE; goal_match_bind_step
      | |- match (mem ?s ?w) with _ => _ end = _ => subst s
      | |- _ = match (mem ?s ?w) with _ => _ end => subst s
      | H: (?m ?v) = _ |- match (?m ?w) with _ => _ end = _ => rewrite H
      | H: (?m ?v) = _ |- _ = match (?m ?w) with _ => _ end => rewrite H
      | H: _ = (?m ?v) |- match (?m ?w) with _ => _ end = _ => rewrite <- H
      | H: _ = (?m ?v) |- _ = match (?m ?w) with _ => _ end => rewrite <- H
      end; try done.
            
  
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
    - exfalso. unfold allowed_UB in *.
      destruct strong as [m s1 s3 wf_m pc_s1_s3  color_eq side_eq mem_match reg_match].
      rewrite color_eq in allowed. remember (color_of s3) as comp.
      destruct comp; try contradiction. simpl in *. unfold side_of in side_eq. rewrite <- Heqcomp in side_eq. simpl in side_eq.
      remember (i \in domm ip) as cond. simpl in *. unfold Component.id in *.  unfold side_of' in *.
      simpl in *. rewrite <- Heqcond in side_eq.
      destruct cond; try inversion side_eq. eapply Machine.Intermediate.fdisjoint_partition_notinboth.
      + inversion Hmergeable_ifaces as [[_ fdisj] _]. exact fdisj.
      + exact allowed.
      + done. 
    - remember (id s3) as s3'. simpl in Heqs3'. destruct s3' as [mem3 regs3 [pc3_val pc3_tag] internal3 cn3].
      rename Heqs3' into eq_s3. rewrite eq_s3 in strong weak common. rewrite eq_s3.
      inversion strong as [? ? ? wf_m pc_s1_s3 color_eq side_eq mem_match reg_match]. subst m.
      inversion common as [? ? ? ? n tag_pc1 tag_pc2 tag_pc3 wfst end_s1 end_s2 end_s3 code_left code_right]. subst s0 s4 s5.
      inversion step_1; eexists; exists M; simpl; unfold step1 (*;
      (match goal with
       | H: (same_pc _ ?a ?b), eq1 : (?a = _), eq2 : (_ = ?b) |- _ =>
           unfold same_pc in *; oapp_False; oapp_False; rewrite eq1 in H; rewrite <- eq2 in H
           ; simpl in H
       end)*) .
      + split.
        * eapply (plus_left _ [::]); try eapply step_nop; eauto.
          -- eapply (etrans _ (PC)).
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules in *.
             unfold_all.
             repeat (goal_match_bind_step; [simpl|exfalso]).
             admit.
             admit.
             { (* TODO: automate this *)
             unfold evi in *. unfold_all.
             assert (eq: color_of s1 = Some (color ti0)).
             { unfold color_of. rewrite ST. simpl. rewrite PC. done. }
             pose proof (reg_match (color ti0) rcom a eq) as [_ impl].
             destruct (impl (esym Heqa4)) as [d' [d'_match d'_eq]]. rewrite d'_eq in Heqa3. inversion Heqa3. }
          -- eapply star_refl.
          -- done.
        * unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules in *.
          unfold_all. unfold_match.
          unfold_all; try (clear -Heqa2; repeat unfold_match; done).
          rewrite ST in end_s1 Heqa2. simpl in *.
          assert (tpc1 = tpc0) by (clear -Heqa2; unfold mvec in *; unfold_match). subst tpc1.
          (* I can't prove those equalities from Heqa2 due to an issue with dependant types *)
          assert (ti1 = ti0) by admit. subst ti1.
          destruct (end_s1 pc0 _ PC) as [ | [[i' ti'] [Heqi' code_i']]].
          { destruct ti0. simpl in *. auto. unfold_match' Heqa5. }
          { simpl in H2. rewrite <- Heqa1 in H2. simpl in *. rewrite H3 in H2. done. }
          simpl in Heqi'. rewrite Heqi' in Heqa2. unfold mvec in Heqa2. inversion Heqa2.
          unfold check_belong, belong in *.
          repeat (unfold_all || unfold_match). convert_eq_op. 
          subst s s' m is_code0.
          destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? eq_comp eq_off pc_s1_s3].
          { exfalso. rewrite ST in eq_none. simpl in *. rewrite eq_none in PC. done. }
          assert (comp = color).
          { unfold color_of in eq_comp.  rewrite ST PC in eq_comp. simpl in *. congruence. } 
          subst comp.
          eapply (preserves_equiv_left_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)@(taga (pc s1)))
                                                   (pc3' := (addw (vala (pc s3)) onew)@(taga (pc s3))); eauto.
          -- rewrite ST. simpl. inv Heqa0. done.
          -- rewrite ST. eapply same_pc_normal; simpl; eauto.
             ++ rewrite Heqi'. done.
             ++ rewrite pc_s1_s3 ST. simpl. rewrite <- (addwA pc0 _). rewrite (addwC (as_word _) onew). rewrite addwA. done.
          -- rewrite ST. simpl. rewrite PC Heqi'. simpl. done.
          -- deduct_color_eq. 
             simpl in *. rewrite <- color_eq. rewrite PC. simpl. 
             rewrite PC in color_eq.
             let comp_in := fresh "comp_in" in
             let t := fresh "t" in
             let t_color := fresh "t_color" in
             let t_code  := fresh "t_code" in
             let impl  := fresh "impl" in
             match goal with
             | eq_off: (_ _ = Some ?off), side_eq: side_of _ = _, pc_s1_s3: _ = (addw _ (as_word ?off)),
                     code_left: combined_codes Left _ _ _, code: is_true ?isc,
                         Heqi': ?mem0 ?w = Some ?v@(MTag ?vt ?comp ?e ?isc),
                           color_eq : _ = match (?mem3 _) with _ => _ end |-
                 _ = match (?mem3 _) with _ => _ end =>
                 remember (MTag vt comp e isc) as t;
                 unfold combined_codes, side_of, side_of' in *; unfold_all; unfold_match;                 
                 match goal with
                 | H : true = (@in_mem ?T ?comp ?s) |- _ =>
                     assert (comp_in: @in_mem T comp s) by (rewrite <- H; done); 
                     assert (t_color: LRC.color t = comp) by (subst; auto);
                     assert (t_code : LRC.is_code t) by (subst; done);
                     destruct (code_left w (v@t) off comp comp_in eq_off t_code t_color) as [_ impl];
                     try (rewrite (addwC _ onew) in impl; rewrite <- (addwA _ _ _) in impl);
                     rewrite <- pc_s1_s3 in impl;
                     repeat (rewrite (addwC onew _) in impl);
                     rewrite (impl Heqi'); subst; done
                 end
             end. (* color *) (* todo : color automation using end_s3 and code_left *)
      + split.
        * eapply (plus_left _ [::]); try eapply step_const; eauto.
          -- eapply (etrans _ (PC)).
          -- eapply (etrans _ (OLD)).
          -- admit.
          -- eapply star_refl.
          -- done.
        * unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules in *.
          unfold_all.
          unfold_match.
          unfold_all; try (clear -Heqa2; repeat unfold_match; done).
          unfold_match. unfold_all.
          unfold switch_val in *. simpl in *. subst p1. unfold_all. unfold_match' Heqa0. subst p2.
          unfold_all. simpl in *. unfold_match' Heqa4. unfold_all. repeat unfold_match' Heqa7.
          unfold_all. inversion Heqa0. subst tpc1 tr0. simpl in *.
          assert (trpc0 = tpc0) by (clear -Heqa2; unfold mvec in *; unfold_match). subst tpc0.
          eapply preserves_equiv_left_reg_write with (r := r) (v := (swcast n0)@Other) (v' := (swcast n0)@Other); simpl.
          eapply preserves_equiv_left_pc_incr with (pc1' := (addw (vala (pc s1)) onew)@(taga (pc s1)))
                                                   (pc3' := (addw (vala (pc s3)) onew)@(taga (pc s3))); simpl; eauto; try done.
          --  destruct pc_s1_s3 as [? ? ? eq_none|? ? ? ? eq_comp eq_off pc_s1_s3].
             ++ exfalso. rewrite ST in eq_none. simpl in *. rewrite eq_none in PC. done.
             ++ eapply same_pc_normal. simpl. admit. admit. admit. (*need hypothesis for this case*)
          -- admit. (* color *)
          -- admit. (* color *)
          -- split; auto.
          -- admit. (* color *)
          -- unfold updm. simpl.
             rewrite ST OLD. simpl. done.
          -- unfold updm. simpl.
             destruct (reg_match (color ti0) r old@told) as [_ impl]; auto.
                ** simpl. unfold side_of in *. rewrite ST. simpl. rewrite PC. done.
                ** rewrite ST in impl. simpl in impl. destruct (impl OLD) as [d' [d'_match eq]]. rewrite eq. simpl. done.
          -- simpl. rewrite ST. done.
          -- simpl. done.
          -- simpl. admit. (* color *)
          -- done.
      + admit.
      + admit.
      + admit.
      + split.
        * eapply (plus_left _ [::]); try eapply step_store; eauto.
          -- eapply (etrans _ (PC)).
          -- eapply (etrans _ (R1W)).
          -- eapply (etrans _ (R2W)).
          -- eapply (etrans _ (OLD)).
          -- admit. (* need hypothesis *)
          -- eapply star_refl.
          -- done.
        * unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules in *.
          unfold_all.
          unfold_match.
          unfold_all; try (clear -Heqa2; repeat unfold_match; done).
          do 4 unfold_match' Heqa7.
          unfold_all.
          (* I can't prove those equalities from Heqa2 due to an issue with dependant types *)
          assert (ti1 = ti0) by admit.
          assert (v = t1) by admit.
          assert (v0 = t2) by admit.
          assert (m0 = told) by admit.
          subst ti1 v v0 m0.
          unfold check_belong, belong in *. unfold_match' Heqa5.
          rewrite ST in end_s1 Heqa2. simpl in *.
          destruct (end_s1 pc0 _ PC) as [ | [[i' ti'] [Heqi' code_i']]].
          { destruct ti0. simpl in *. auto. unfold_match' Heqa5. }
          { simpl in H2. rewrite <- Heqa1 in H2. simpl in *. rewrite H3 in H2. done. }
          simpl in Heqi'. rewrite Heqi' in Heqa2. unfold mvec in Heqa2. inversion Heqa2.
          unfold check_belong, belong in *.
          repeat (unfold_all || unfold_match). convert_eq_op.
          destruct ((reg_match (color ti0) r2 (w2@t2))) as [_ impl].
          unfold color_of. rewrite ST PC Heqa24. done. rewrite ST in impl.
          destruct (impl R2W) as [v' [v'_match v'_eq]]. clear impl.
          destruct ((reg_match (color ti0) r1 (w1@t1))) as [_ impl].
          unfold color_of. rewrite ST PC Heqa24. done. rewrite ST in impl.
          destruct (impl R1W) as [v'' [v''_match v''_eq]]. clear impl.
          unfold switch_val in *. destruct told. simpl in *. inversion Heqa18. unfold_all. inversion Heqa11.
          inversion Heqa26. subst p1 p2 vtag1 color1 entry1 is_code0 is_code1 is_code2 tni0.
          simpl in *. remember ({| vtag := t2; color := LRC.color ti0; entry := entry2; is_code := false |}) as t2'.
          assert (color_of s1 = Some (LRC.color ti0)) as c_eq.
          { unfold color_of. rewrite ST. rewrite PC. simpl. subst ti0. simpl in *. done. }
          remember (if is_address t2 then Invalidated else Other) as new_t2.
          destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? eq_comp eq_off pc_s1_s3].
          { exfalso. rewrite ST in eq_none. simpl in *. rewrite eq_none in PC. done. }
          assert (comp = color).
          { unfold color_of in eq_comp.  rewrite ST PC in eq_comp. simpl in *. congruence. } 
          subst comp.
          eapply preserves_equiv_left_reg_write with (r := r2) (v := w2@new_t2) (v' := (vala v')@new_t2); simpl.
          eapply preserves_equiv_left_reg_write with (r := r1) (v := w1@t1) (v' := v''); simpl.
          eapply preserves_equiv_left_mem_write with (v := w2@t2') (v' := (vala v')@t2') (w := w1); simpl.
          eapply preserves_equiv_left_pc_incr with (pc1' := (addw (vala (pc s1)) onew)@(taga (pc s1)))
                                                   (pc3' := (addw (vala (pc s3)) onew)@(taga (pc s3))); simpl; eauto.
          -- rewrite ST. eapply same_pc_normal; simpl; eauto.
             ++ rewrite Heqi'. simpl. done.
             ++ rewrite pc_s1_s3 ST. simpl. rewrite <- (addwA pc0 _). rewrite (addwC (as_word _) onew). rewrite addwA. done.
          -- deduct_color_eq.
          -- deduct_color_eq. admit. (* color *) (* todo : color automation using end_s3 and code_left *)
          -- unfold data_match'. split; auto.
             simpl in *.
             unfold color_of in c_eq. rewrite ST PC in c_eq. inv c_eq.
             assert (t2 = taga v') by (destruct v'; destruct v'_match; auto). destruct v'. simpl in *. auto. subst t2. auto.
          -- done.
          -- subst t2'. simpl. clear -c_eq side_eq color_eq. unfold side_of in *. rewrite <- color_eq, c_eq in side_eq.
             inv side_eq. unfold side_of' in *. unfold_match.
          -- subst t2'. simpl. intros v disj. destruct disj.
             ++ rewrite ST in H6. simpl in *. rewrite OLD in H6. inv H6. simpl in *. done.
             ++ destruct (mem_match w1 old@({| vtag := vtag2; color := color; entry := entry2; is_code := false |})) as [_ impl]; auto.
                ** simpl. unfold side_of in *. rewrite <- color_eq, c_eq in side_eq.
                   inv side_eq. unfold side_of' in *. unfold_match.
                ** rewrite ST in impl. simpl in impl. destruct (impl OLD) as [d' [d'_match eq]]. rewrite eq in H6. inv H6.
                   destruct v.  destruct d'_match. simpl in *. rewrite <- H. done. 
          -- subst t2'. simpl.
             destruct (mem_match w1 old@({| vtag := vtag2; color := color; entry := entry2; is_code := false |})) as [_ impl]; auto.
                ** simpl. unfold side_of in *. rewrite <- color_eq, c_eq in side_eq.
                   inv side_eq. unfold side_of' in *. unfold_match.
                ** rewrite ST in impl. destruct (impl OLD) as [d' [d'_match eq]]. exists d'. split; auto.
                   destruct d'. destruct d'_match. simpl in *. subst. simpl. done. 
          -- subst t2'. simpl. exists (old@({| vtag := vtag2; color := color; entry := entry2; is_code := false |})).
             split; auto. rewrite ST. done.
          -- subst t2'. done. 
          -- subst t2'. done. 
          -- subst t2'. unfold updm. simpl.
             rewrite ST OLD. simpl. done.
          -- subst t2'. unfold updm. simpl.
             destruct (mem_match w1 old@({| vtag := vtag2; color := color; entry := entry2; is_code := false |})) as [_ impl]; auto.
                ** simpl. unfold side_of in *. rewrite <- color_eq, c_eq in side_eq.
                   inv side_eq. unfold side_of' in *. unfold_match.
                ** rewrite ST in impl. simpl in impl. destruct (impl OLD) as [d' [d'_match eq]]. rewrite eq. simpl. done. 
          -- done.
          -- done.
          -- rewrite ST. simpl.
             rewrite setmE. remember (@eq_op (Ord.eqType _) (addw pc0 onew) w1) as cond. simpl in *. rewrite <- Heqcond.
             destruct cond; try auto. assert ((addw pc0 onew) = w1) by (clear -Heqcond; eq_op_to_eq). subst w1.
             rewrite OLD. subst. done. (* color *)
          -- rewrite <- eq_s3. simpl. admit. (* color *)  (* todo : color automation using end_s3 and code_left *)
          -- eauto.
          -- rewrite ST. simpl.
             rewrite setmE. remember (@eq_op (Ord.eqType _) (addw pc0 onew) w1) as cond. simpl in *. rewrite <- Heqcond.
             destruct cond.
             ++ subst. simpl. done.
             ++ rewrite Heqi'. simpl. subst ti0. done. (* color *)
          -- subst t2'. rewrite ST. unfold updm. simpl. rewrite R1W. simpl. done.
          -- subst t2'. unfold updm. simpl.
             destruct (reg_match color r1 (w1@t1)) as [_ impl]; subst ti0; auto. 
             rewrite ST in impl. simpl in impl. destruct (impl R1W) as [d' [d'_match eq]]. rewrite eq. simpl. done. 
          -- done. 
          -- done. 
          -- done. 
          -- done. 
          -- split; auto. unfold_match' Heqnew_t2. subst new_t2.
             destruct v'. destruct v'_match. unfold is_address in *. unfold_match.
          -- simpl. rewrite ST.
             rewrite setmE. remember (@eq_op (Ord.eqType _) (addw pc0 onew) w1) as cond. 
             simpl in *. rewrite <- Heqcond. destruct cond. subst t2' ti0. simpl. done.
             rewrite Heqi'. done. (* color *)
          -- subst t2'. rewrite ST. unfold updm. simpl.
             remember (setm reg r1 w1@t1 r2) as val. destruct val; try done.
             exfalso. rewrite setmE in Heqval. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             rewrite <- Heqcond in Heqval. destruct cond; try done. rewrite R2W in Heqval. done.
          -- subst t2'. unfold updm. simpl.
             remember (setm (regs s3) r1 v'' r2) as val. simpl in *.
             rewrite <- Heqval. destruct val; try done.
             exfalso. rewrite setmE in Heqval. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             rewrite <- Heqcond in Heqval. destruct cond; try done.
             destruct (reg_match color r2 (w2@t2)) as [_ impl]; subst ti0; auto.
             rewrite ST in impl. simpl in impl. destruct (impl R2W) as [d' [d'_match eq]]. rewrite eq in Heqval. done. 
          -- simpl.
             rewrite ST. simpl in *. inversion Heqa11.
             simpl. remember (@eq_op (Ord.eqType _) r2 r1) as cond. destruct cond.
             ++ assert (r2 = r1) by (clear - Heqcond; eq_op_to_eq).
                subst r2. do 2 rewrite setmxx.
                rewrite ST in Heqa20. simpl in *. rewrite setmE in Heqa21. simpl in *.
                remember (@eq_op (Ord.eqType _) r1 r1) as tmp. simpl in *. rewrite <- Heqtmp in Heqa21.
                destruct tmp; try (rewrite eq_refl in Heqtmp; done). simplify_some. simpl.
                rewrite R2W in Heqa20. simplify_some. simpl. inv Heqa0. simpl. done.
             ++ rewrite ST in Heqa20. simpl in *. rewrite setmE in Heqa21. simpl in *.
                remember (@eq_op (Ord.eqType _) r1 r1) as tmp. simpl in *. rewrite <- Heqcond in Heqa21.
                destruct tmp; try (rewrite eq_refl in Heqtmp; done). rewrite R1W in Heqa20. simplify_some.
                rewrite ST in Heqa21. simpl in *. rewrite R2W in Heqa21. simplify_some. simpl. inv Heqa0. simpl. done.
          -- simpl. admit. (* weird state behavior? *)
          -- simpl. admit. (* color *)
          -- simpl. admit. (* color *)
      + admit.
      + admit.
      + unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules in *.
        unfold_all.
        unfold_match.
        unfold_all; try (clear -Heqa2; repeat unfold_match; done).
        unfold_match. admit.
      + admit.
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

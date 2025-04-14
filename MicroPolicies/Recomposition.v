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

Require Import MicroPolicies.Utils.
Import DoNotation.

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
    Component.main \in domm (prog_interface p) <-> prog_main p
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
    fun '(Symbolic.State m _ (Types.Atom pc _) _ _) =>
      match (m pc) with
      | None => None
      | Some (Types.Atom _ tag) => Some (color tag)
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

  Section SimulationRelations.

    Variant side := Left | Right.

    Definition other_side s := match s with Left => Right | Right => Left end.

    Definition side_of (s: state): option side :=
        do! c <- color_of s;
           if c \in domm ip then
             Some Left
           else
             Some Right.

    
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

    Definition find_rank {T} (f: pred T) (l: seq T) : option nat := find_rank' f l 0.
    (* Todo: write a lemma (about find_rank) usable along get_procedures and well_formed_program *)
    
    Definition p0 (prog: program) (comp: Component.id): option nat :=
      do! start <- find_rank (fun '(_,tag) => color tag == comp) (code prog);
      Some (start + size (domm (@initial_memory mt (prog_buffers prog)))).
    
    Definition offset1: NMap ssrint.int :=
      mkfmapfp (fun comp => do! p_s3 <- p0 prog'' comp; 
                         do! p_s1 <- p0 prog comp;
                         Some (encode_int (Z.pos_sub (Pos.of_nat p_s3) (Pos.of_nat p_s1)))) (domm ip).
    
    Definition offset2: NMap ssrint.int := 
      mkfmapfp (fun comp => do! p_s3 <- p0 prog'' comp; 
                         do! p_s2 <- p0 prog comp;
                         Some (encode_int (Z.pos_sub (Pos.of_nat p_s3) (Pos.of_nat p_s2)))) (domm ip).
    
    Record metadata :=
      { stack: seq (stack_value * stack_value * stack_value * Component.id )%type;
        (*
        offset1: NMap ssrint.int;
        offset2: NMap ssrint.int;
        offset1_complete: domm offset1 = domm ip;
        offset2_complete: domm offset2 = domm ic; *)
      }.

    Fixpoint correct_levels (s : seq (stack_value * stack_value * stack_value * Component.id )) : Prop :=
      match s with
      | [] => True
      | ((Types.Atom _ t1), (Types.Atom _ t2), (Types.Atom _ t3), c) :: s' =>
          t1 = t2 /\ t2 = t3 /\ t1 = Ret (size s') /\ (c \in domm ip \/ c \in domm ic) /\ correct_levels s'
      end.

    Definition contains_value (s : state) (v : stack_value) : Prop :=
      (exists w v', mem s w = Some v' /\ v = Types.Atom (Types.vala v') (vtag (Types.taga v')) ) \/
        (exists w v', regs s w = Some v' /\ v = Types.Atom (Types.vala v') (Types.taga v') ).
    
    Definition get_offset i comp :=
      match i with
      | Left => offset1 comp
      | Right => offset2 comp
      end.

    Definition points_to_comp_code (s : state) (v : stack_value) (comp : Component.id) : Prop :=
      Option.apply (fun memval => color (Types.taga (memval)) = comp) False (mem s (Types.vala v)).
    (* this might need to check that is_code is true in some conditions *)
    
    Definition well_formed_metadata (i : side) (m: metadata) s s' : Prop :=
        (correct_levels (stack m) /\
           forall v1 v2 v3 v c off,
             In (v1, v2, v3, c) (stack m) ->
             (match i with Left => v1 | Right => v2 end) = v ->
             get_offset i c = Some off ->
             points_to_comp_code s v c /\
               points_to_comp_code s' v3 c /\
               (is_relevant_comp i c -> contains_value s v -> contains_value s' v3) /\
               (is_relevant_comp i c -> (Types.vala v3) = addw (Types.vala v) (as_word off))).
    (* todo : sanity check *)

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
                | Left  => exists sv', In (d, sv', d', comp) (stack m)
                | Right => exists sv', In (sv', d, d', comp) (stack m)
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
        ((mem s' w) = Some d -> exists d', data_match' i m d d' /\ (mem s  w) = Some d') /\
          ((mem s  w) = Some d -> exists d', data_match' i m d d' /\ (mem s' w) = Some d').

    Definition registers_match (i: side) (m: metadata) (s: state) (s': state) : Prop :=
      forall c w d,
        color_of s = Some c ->
        ((regs s' w) = Some d -> exists d', data_match i c m d d' /\ (regs s  w) = Some d') /\
          ((regs s  w) = Some d -> exists d', data_match i c m d d' /\ (regs s' w) = Some d').

    Definition same_pc (i: side) (s: state) (s': state) : Prop :=
      oapp
        (fun comp => oapp (fun off => (Types.vala (pc s')) = addw (Types.vala (pc s)) (as_word off))
                    False (get_offset i comp))
        False (color_of s).

    Definition combined_codes (i: side) (m: metadata) (s: state) (s': state) : Prop :=
      forall w v off c,
        is_relevant_comp i c ->
        get_offset Left c = Some off ->
        is_code (Types.taga v) ->
        color (Types.taga v) = c ->
        ((mem s' (addw w (as_word off)) = Some v) <-> (mem s w = Some v)).
    
    Variant common_equiv: metadata -> state -> state -> state -> Prop :=
        common_equiv_def : forall m s1 s2 s3,
            combined_codes Left  m s1 s3 ->
            combined_codes Right m s2 s3 ->
            common_equiv m s1 s2 s3
    .
    Variant strong_equiv (i: side): metadata -> state -> state -> Prop :=
      strong_equiv_def : forall m s s',
          well_formed_metadata i m s s' ->
          same_pc i s s' ->
          color_of s <> None ->
          color_of s = color_of s' ->
          side_of s' = Some i ->
          memory_match i m s s' ->
          registers_match i m s s' ->
          strong_equiv i m s s'
    .

    Variant weak_equiv (i: side): metadata -> state -> state -> Prop :=
      weak_equiv_def : forall m s s',
          well_formed_metadata i m s s' ->
          color_of s = color_of s' ->
          side_of s' = Some (other_side i) ->
          memory_match i m s s' ->
          weak_equiv i m s s'
    .


  End SimulationRelations.

  Notation match_states := (match_states sem sem' sem'' (common_equiv)
    (strong_equiv Left) (strong_equiv Right) (weak_equiv Left) (weak_equiv Right)).

  
  Lemma match_initial_states:
  forall s1, Smallstep.initial_state sem s1 ->
  forall s2, Smallstep.initial_state sem' s2 ->
  exists s3 M, Smallstep.initial_state sem'' s3 /\ match_states M s1 s2 s3.
  Proof.
    intros s1 init1 s2 init2.
    unfold Smallstep.initial_state, sem, sem' in init1, init2. simpl in init1. unfold initial_state1, initial_state2 in *.
    remember (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')) as s3.
    exists s3. exists ({|stack := []|}).
    split; try (simpl; unfold initial_state3; done).
    remember (prog_main p) as main. destruct main; [eapply match_states_left | eapply match_states_right]; econstructor; simpl.
    - unfold combined_codes. intros.
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
    remember (@Exec.stepf _ _ _ Merged.transfer _ table s3) as s3'.
    destruct step_s1 as [s1 ? s1' step_2 allowed | s1 ? s1' step_1 step_2]; subst t.
    - exfalso. unfold allowed_UB in *.
      destruct strong as [m s1 s3 wf_m pc_s1_s3 color_ineq color_eq side_eq mem_match reg_match].
      rewrite color_eq in allowed. remember (color_of s3) as comp.
      destruct comp; try contradiction. simpl in *. unfold side_of in side_eq. rewrite <- Heqcomp in side_eq. simpl in side_eq.
      remember (i \in domm ip) as cond. simpl in *. unfold Component.id in *. rewrite <- Heqcond in side_eq.
      destruct cond; try inversion side_eq. eapply Machine.Intermediate.fdisjoint_partition_notinboth.
      + inversion Hmergeable_ifaces as [[_ fdisj] _]. exact fdisj.
      + exact allowed.
      + done. 
    - destruct s3' as [[s3' ev]|].
      + exists s3', M. admit.
      + exfalso. unfold step2, step1, step_mp, step_me in step_1, step_2. simpl in step_1, step_2.
        setoid_rewrite <- Exec.stepP in step_1. setoid_rewrite <- Exec.stepP in step_2.
        destruct strong as [m s1 s3 wf_m pc_s1_s3 color_ineq color_eq side_eq mem_match reg_match].
        unfold same_pc in *.
        destruct (color_of s1) as [comp|]; try contradiction; simpl in pc_s1_s3.
        remember (offset1 comp) as off.
        destruct off as [off|]; try contradiction; simpl in pc_s1_s3.
        destruct common as [m s1 s2 s3 code_s1 code_s2].
        remember (mem s1 (Types.vala (pc s1))) as instr.
        destruct instr. admit. unfold Exec.stepf in step_1. destruct s1, pc0. simpl in *. rewrite <- Heqinstr in step_1.
        simpl in step_1. inversion step_1.
        destruct (code_s1 (pc s1) _ off comp).
        admit.
  Admitted.
      (*Set Printing All.*) 

      
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

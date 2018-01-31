Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From CoqUtils Require Import ord fset fmap.

Local Open Scope fset_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Inductive expr : Type :=
| E_val : value -> expr
| E_local : expr
| E_binop : binop -> expr -> expr -> expr
| E_seq : expr -> expr -> expr
| E_if : expr -> expr -> expr -> expr
| E_alloc : expr -> expr
| E_deref : expr -> expr
| E_assign : expr -> expr -> expr
| E_call : Component.id -> Procedure.id -> expr -> expr
| E_exit : expr.

Fixpoint called_procedures (e : expr) : {fset Component.id * Procedure.id} :=
  match e with
  | E_binop _ e1 e2 => called_procedures e1 :|: called_procedures e2
  | E_seq e1 e2 => called_procedures e1 :|: called_procedures e2
  | E_if e1 e2 e3 => called_procedures e1 :|: called_procedures e2
                     :|: called_procedures e3
  | E_alloc e => called_procedures e
  | E_deref e => called_procedures e
  | E_assign e1 e2 => called_procedures e1 :|: called_procedures e2
  | E_call C P e => (C, P) |: called_procedures e
  | _ => fset0
  end.

Module Source.
  Record program : Type := mkProg {
    prog_interface : Program.interface;
    prog_procedures : NMap (NMap expr);
    prog_buffers : NMap (nat + list value);
    prog_main : option (Component.id * Procedure.id)
  }.

  (* useful function on closed programs *)
  Definition main_comp (p: Source.program): Component.id :=
    match prog_main p with
    | Some (mainC, _) => mainC
    | None => 0
    end.

  (** Lookup definition of procedure [C.P] in the map [procs]. *)
  Definition find_procedure
             (procs: NMap (NMap expr))
             (C: Component.id) (P: Procedure.id) : option expr :=
    match procs C with
    | Some C_procs => C_procs P
    | None         => None
    end.

  Definition valid_calls
             (procs: NMap (NMap expr))
             (intf: Program.interface)
             (cur_comp: Component.id)
             (calls: {fset Component.id * Procedure.id}) :=
    forall C P, (C, P) \in calls ->
      if C == cur_comp then find_procedure procs cur_comp P : Prop
      else imported_procedure intf cur_comp C P.

  Fixpoint values_are_integers (e: expr) : bool :=
    match e with
    | E_val (Int _)   => true
    | E_val _         => false
    | E_local         => true
    | E_exit          => true
    | E_binop _ e1 e2 => values_are_integers e1 && values_are_integers e2
    | E_seq     e1 e2 => values_are_integers e1 && values_are_integers e2
    | E_if   e1 e2 e3 => [&& values_are_integers e1, values_are_integers e2 &
                             values_are_integers e3]
    | E_alloc e       => values_are_integers e
    | E_deref e       => values_are_integers e
    | E_assign  e1 e2 => values_are_integers e1 && values_are_integers e2
    | E_call   _ _ e  => values_are_integers e
    end.

  (* An expression is well-formed when:
     1) calls outside the component are allowed by the interface
     2) calls inside the component are targeting existing procedures
     3) the undef value is not present
     4) pointers are not present (no pointer forging) *)
  Definition well_formed_expr (p: program) (cur_comp: Component.id) (e: expr) : Prop :=
    valid_calls (prog_procedures p) (prog_interface p) cur_comp (called_procedures e)
    /\ values_are_integers e.

  (* Component C has a buffer of size at least one *)
  Definition has_required_local_buffers (p: program) (C: Component.id) : Prop :=
    exists2 buf, prog_buffers p C = Some buf &
                 match buf with
                 | inl size   => size > 0
                 | inr values => length values > 0
                 end%nat.

  Record well_formed_program (p: program) := {
    (* the interface is sound (but maybe not closed) *)
    wfprog_interface_soundness:
      sound_interface (prog_interface p);
    (* there are procedures only for the declared components *)
    wfprog_well_formed_procedures_1:
      fsubset (domm (prog_procedures p)) (domm (prog_interface p));
    (* each exported procedure is actually defined *)
    wfprog_exported_procedures_existence:
      forall C P, exported_procedure (prog_interface p) C P ->
      find_procedure (prog_procedures p) C P;
    (* each instruction of each procedure is well-formed *)
    wfprog_well_formed_procedures_2:
      forall C P Pexpr,
        find_procedure (prog_procedures p) C P = Some Pexpr ->
        well_formed_expr p C Pexpr;
    (* each declared component has the required static buffers *)
    wfprog_defined_buffers: domm (prog_interface p) = domm (prog_buffers p);
    (* each component's buffer is well formed *)
    wfprog_well_formed_buffers:
      forall C, prog_interface p C ->
                has_required_local_buffers p C;
    (* if the main component exists, then the main procedure must exist as well *)
    wfprog_main_existence:
      forall mainC mainP,
        prog_main p = Some (mainC, mainP) ->
        find_procedure (prog_procedures p) mainC mainP
  }.

  (* a closed program is a program with a closed interface and an existing main
     procedure *)
  Record closed_program (p: program) := {
    (* the interface must be closed (and consequently sound) *)
    cprog_closed_interface:
      closed_interface (prog_interface p);
    (* the main procedure must exist *)
    cprog_main_existence:
      exists mainC mainP main_procs,
        prog_main p = Some (mainC, mainP) /\
        prog_procedures p mainC = Some main_procs /\ mainP \in domm main_procs
  }.

  Theorem linkable_disjoint_procedures :
    forall prog1 prog2,
      well_formed_program prog1 ->
      well_formed_program prog2 ->
      linkable (prog_interface prog1) (prog_interface prog2) ->
      fdisjoint (domm (prog_procedures prog1)) (domm (prog_procedures prog2)).
  Proof.
    move=> p1 p2 wf1 wf2 [sound_intf dis].
    apply: (fdisjoint_trans (wfprog_well_formed_procedures_1 wf1)).
    rewrite fdisjointC.
    apply: (fdisjoint_trans (wfprog_well_formed_procedures_1 wf2)).
    by rewrite fdisjointC.
  Qed.

  Theorem linkable_disjoint_buffers :
    forall prog1 prog2,
      well_formed_program prog1 ->
      well_formed_program prog2 ->
      linkable (prog_interface prog1) (prog_interface prog2) ->
      fdisjoint (domm (prog_buffers prog1)) (domm (prog_buffers prog2)).
  Proof.
    move=> p1 p2 wf1 wf2 [].
    by rewrite (wfprog_defined_buffers wf1) (wfprog_defined_buffers wf2).
  Qed.

  (* AAA: I think this does not follow from the definition of linkable, because
     there is nothing in the interface that talks about main.  We might have to
     add linkable_mains into the definition of linkable. *)
  Theorem linkable_disjoint_mains :
    forall prog1 prog2,
      well_formed_program prog1 ->
      well_formed_program prog2 ->
      linkable (prog_interface prog1) (prog_interface prog2) ->
      linkable_mains (prog_main prog1) (prog_main prog2).
  Proof.
    move=> p1 p2 wf1 wf2 [sound dis]; rewrite /linkable_mains.
    case p1_main: (prog_main p1)=> [[mainC mainP]|] //=.
    move/(wfprog_main_existence wf1) in p1_main.
    have {p1_main} p1_main: mainC \in domm (prog_procedures p1).
      move: p1_main; rewrite mem_domm /find_procedure.
      by case: (prog_procedures p1 mainC).
    move/fsubsetP/(_ _ p1_main): (wfprog_well_formed_procedures_1 wf1)=> {p1_main} p1_main.
    move/fdisjointP/(_ _ p1_main): dis.
  Admitted.

  Definition program_link (p1 p2: program) : program :=
    {| prog_interface := unionm (prog_interface p1) (prog_interface p2);
       prog_procedures := unionm (prog_procedures p1) (prog_procedures p2);
       prog_buffers := unionm (prog_buffers p1) (prog_buffers p2);
       prog_main := main_link (prog_main p1) (prog_main p2) |}.

  Lemma linkable_programs_has_component p1 p2 :
    linkable (prog_interface p1) (prog_interface p2) ->
    forall C CI,
      Program.has_component (unionm (prog_interface p1) (prog_interface p2)) C CI
      <-> Program.has_component (prog_interface p1) C CI
          \/ Program.has_component (prog_interface p2) C CI.
  Proof.
    case=> sound_int dis_ints C CI.
    rewrite /Program.has_component !unionmE.
    case if_p1_C: (prog_interface p1 C)=> [CI'|] //=.
    - split; try tauto.
      case=> [//|if_p2_C].
      move/fdisjointP/(_ C): dis_ints.
      rewrite !mem_domm if_p1_C => /(_ erefl).
      by rewrite if_p2_C.
    - split; try tauto.
      by case.
  Qed.

  Lemma linkable_programs_find_procedure p1 p2 :
    well_formed_program p1 ->
    well_formed_program p2 ->
    linkable (prog_interface p1) (prog_interface p2) ->
    forall C P Pexpr,
      find_procedure (unionm (prog_procedures p1) (prog_procedures p2)) C P = Some Pexpr
      <-> find_procedure (prog_procedures p1) C P = Some Pexpr
          \/ find_procedure (prog_procedures p2) C P = Some Pexpr.
  Proof.
    move=> wf1 wf2 link C P Pexpr.
    move/(linkable_disjoint_procedures wf1 wf2) in link.
    move/fdisjointP/(_ C)/implyP: link.
    rewrite /find_procedure unionmE !mem_domm.
    case p1_C: (prog_procedures p1 C)=> [Cprocs|] //=.
    - by case: (prog_procedures p2 C)=> // _; intuition congruence.
    - by intuition congruence.
  Qed.

  Lemma linkable_programs_find_procedure_dom p1 p2 :
    well_formed_program p1 ->
    well_formed_program p2 ->
    linkable (prog_interface p1) (prog_interface p2) ->
    forall C P,
      find_procedure (unionm (prog_procedures p1) (prog_procedures p2)) C P
      = find_procedure (prog_procedures p1) C P
        || find_procedure (prog_procedures p2) C P :> bool.
  Proof.
    move=> wf1 wf2 link C P.
    move/(linkable_disjoint_procedures wf1 wf2) in link.
    move/fdisjointP/(_ C)/implyP: link.
    rewrite /find_procedure unionmE !mem_domm.
    case p1_C: (prog_procedures p1 C)=> [Cprocs|] //=.
    by rewrite orbC; case: (prog_procedures p2 C)=> // _.
  Qed.

  Lemma linkable_imported_procedure p1 p2 :
    linkable (prog_interface p1) (prog_interface p2) ->
    forall C C' P,
      imported_procedure (unionm (prog_interface p1) (prog_interface p2)) C C' P
      <-> imported_procedure (prog_interface p1) C C' P
          \/ imported_procedure (prog_interface p2) C C' P.
  Proof.
    move=> link C C' P.
    rewrite /imported_procedure /Program.has_component /Component.is_importing.
    rewrite unionmE; split.
    - case=> CI [].
      case p1_C: (prog_interface p1 C)=> [CI'|] //=; by eauto.
    - case => [[CI [get_CI in_CI]]|[CI [get_CI in_CI]]].
        by rewrite get_CI /=; eauto.
      case: link=> _ dis.
      move: dis; rewrite fdisjointC=> /fdisjointP/(_ C).
      rewrite !mem_domm get_CI => /(_ erefl).
      by case: (prog_interface p1 C)=> [|] //=; eauto.
  Qed.

  Theorem linking_well_formedness:
    forall p1 p2,
      well_formed_program p1 ->
      well_formed_program p2 ->
      linkable (prog_interface p1) (prog_interface p2) ->
      well_formed_program (program_link p1 p2).
  Proof.
    move=> p1 p2 wf1 wf2 link.
    split; try by case: link.
    - by case: link => *; rewrite !domm_union fsetUSS // wfprog_well_formed_procedures_1.
    - move=> C P [CI []].
      rewrite (linkable_programs_has_component link) /= => has_C_CI exp_CI_P.
      rewrite linkable_programs_find_procedure_dom //; apply/orP.
      by case: has_C_CI=> [H|H]; [left|right];
      apply: wfprog_exported_procedures_existence=> //; exists CI; eauto.
    - move=> C P Pexpr.
      rewrite /= (linkable_programs_find_procedure wf1 wf2 link) => find.
      have {find} wf: well_formed_expr p1 C Pexpr \/ well_formed_expr p2 C Pexpr.
        case: find=> [H|H]; [left|right];
        apply: wfprog_well_formed_procedures_2; by case: link; eauto.
      split=> /=; last by case: wf=> [[]|[]].
      without loss {link wf wf1 wf2} [link wf1 wf2 [wf _]]: p1 p2 /
          [/\ linkable (prog_interface p1) (prog_interface p2),
              well_formed_program p1,
              well_formed_program p2 &
              well_formed_expr p1 C Pexpr].
        case: wf=> wf; first by apply; split=> //.
        rewrite (unionmC (linkable_disjoint_procedures wf1 wf2 link)).
        case: (link)=> _ dis_intf; rewrite (unionmC dis_intf); apply.
        by split=> //; apply: linkable_sym.
      move=> /= C' P' /wf {wf}; case: ifP => _.
      + by rewrite linkable_programs_find_procedure_dom // => ->.
      + by rewrite linkable_imported_procedure //; eauto.
    - by rewrite /= !domm_union (wfprog_defined_buffers wf1) (wfprog_defined_buffers wf2).
    - rewrite /has_required_local_buffers /= => C.
      move: (linkable_disjoint_buffers wf1 wf2 link)=> dis_buf.
      move/wfprog_well_formed_buffers in wf1.
      move/wfprog_well_formed_buffers in wf2.
      rewrite -mem_domm domm_union in_fsetU; case/orP; last rewrite unionmC //; rewrite unionmE.
        by rewrite mem_domm; case/wf1=> [? ->] /=; eauto.
      by rewrite mem_domm; case/wf2=> [? ->] /=; eauto.
    - move=> mainC mainP; rewrite /= /main_link /=.
      move: (linkable_disjoint_mains wf1 wf2 link).
      rewrite /linkable_mains.
      rewrite linkable_programs_find_procedure_dom //.
      case Hp1: (prog_main p1)=> [main|] //=.
        by move=> _ [?]; subst main; rewrite (wfprog_main_existence wf1).
      by move=> ??; rewrite (wfprog_main_existence wf2) ?orbT.
  Qed.

  Lemma linked_programs_main_component_origin:
    forall p1 p2,
      well_formed_program p1 ->
      well_formed_program p2 ->
      linkable (prog_interface p1) (prog_interface p2) ->
      closed_program (program_link p1 p2) ->
      main_comp (program_link p1 p2) \in domm (prog_interface p1) \/
      main_comp (program_link p1 p2) \in domm (prog_interface p2).
  Proof.
    move=> p1 p2 wf1 wf2 [_ Hdis] Hclosed.
    have [mainC [mainP [main_procs []]]] := cprog_main_existence Hclosed.
    rewrite /program_link /main_comp /= unionmE => ->.
    (*move/fdisjointP/(_ mainC)/implyP: Hdis.*)
    have/fsubsetP/(_ mainC)/implyP := wfprog_well_formed_procedures_1 wf2.
    have/fsubsetP/(_ mainC)/implyP := wfprog_well_formed_procedures_1 wf1.
    rewrite !mem_domm.
    case: (prog_procedures p1 mainC)=> [main_procs'|] //=; eauto.
    case: (prog_procedures p2 mainC)=> [main_procs'|] //=; eauto.
    by move=> _ _ [].
  Qed.

  Lemma interface_preserves_closedness_l :
    forall p1 p2 p1',
      closed_program (program_link p1 p2) ->
      prog_interface p1 = prog_interface p1' ->
      closed_program (program_link p1' p2).
  Admitted.

  Fixpoint initialize_buffer
           (Cmem: ComponentMemory.t) (b: Block.id) (values: list value)
    : ComponentMemory.t :=
    let fix init m vs i :=
        match vs with
        | [] => m
        | v :: vs' =>
          match ComponentMemory.store m b i v with
          | Some m' =>
            init m' vs' (1+i)%Z
          | None =>
            (* bad case that shouldn't happen, just return memory *)
            init m vs' (1+i)%Z
          end
        end
    in init Cmem values 0%Z.

  Definition prepare_buffers (p: program) : Memory.t * NMap Block.id :=
    (mapm (fun initial_buffer =>
             ComponentMemory.prealloc (mkfmap [(0, initial_buffer)]))
          (prog_buffers p),
     mapm (fun _ => 0) (prog_buffers p)).

  Lemma prepare_buffers_of_linked_programs:
    forall p1 p2,
      well_formed_program p1 ->
      well_formed_program p2 ->
      linkable (prog_interface p1) (prog_interface p2) ->
    forall C b,
      (prepare_buffers (program_link p1 p2)).2 C = Some b ->
      C \notin domm (prog_interface p2) ->
      C \in domm (prog_interface p1) /\ (prepare_buffers p1).2 C = Some b.
  Proof.
    move=> p1 p2 wf1 wf2 Hlinkable C b.
    rewrite /prepare_buffers /= !mapmE unionmE.
    do 2![rewrite wfprog_defined_buffers //=].
    rewrite !mem_domm.
    by case: (prog_buffers p1 C) (prog_buffers p2 C)=> [b'|] //= [b'|].
  Qed.

  Lemma find_procedure_in_linked_programs:
    forall p1 p2,
      well_formed_program p1 ->
      well_formed_program p2 ->
      linkable (prog_interface p1) (prog_interface p2) ->
    forall C P P_expr,
      find_procedure (unionm (prog_procedures p1) (prog_procedures p2)) C P = Some P_expr ->
      C \notin domm (prog_interface p2) ->
      C \in domm (prog_interface p1) /\ find_procedure (prog_procedures p1) C P = Some P_expr.
  Proof.
    move=> p1 p2 wf1 wf2 Hlinkable C P P_expr.
    rewrite linkable_programs_find_procedure // {2}/find_procedure.
    have/fsubsetP/(_ C)/implyP := (wfprog_well_formed_procedures_1 wf2).
    rewrite mem_domm.
    case: (prog_procedures p2 C)=> [C_procs /= ->|] //= _.
    case=> [C_P _|//]; split=> //.
    move/fsubsetP: (wfprog_well_formed_procedures_1 wf1); apply.
    move: C_P; rewrite /find_procedure mem_domm.
    by case: (prog_procedures p1 C).
  Qed.

  Lemma link_sym: forall p c,
      linkable (prog_interface p) (prog_interface c) ->
      program_link p c = program_link c p.
  Admitted.

End Source.

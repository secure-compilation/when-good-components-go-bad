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
    (exists size, getm (prog_buffers p) C = Some (inl size) /\
                  (size > 0)%nat) \/
    (exists values, getm (prog_buffers p) C = Some (inr values) /\
                  (length values > 0)%nat).

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
    wfprog_buffers_existence:
      forall C, C \in domm (prog_interface p) ->
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
        getm (prog_procedures p) mainC = Some main_procs /\ mainP \in domm main_procs
  }.

(*   Inductive linkable_programs: program -> program -> Prop := *)
(*   | linkable_programs_intro: *)
(*       forall prog1 prog2, *)
(*         well_formed_program prog1 -> *)
(*         well_formed_program prog2 -> *)
(*         sound_interface (unionm (prog_interface prog1) (prog_interface prog2)) -> *)
(*         fdisjoint (domm (prog_interface prog1)) (domm (prog_interface prog2)) -> *)
(* (* RB: Stubbing these out to confirm the structure of the high-level proof. *)
(*         fdisjoint (domm (prog_procedures prog1)) (domm (prog_procedures prog2)) -> *)
(*         fdisjoint (domm (prog_buffers prog1)) (domm (prog_buffers prog2)) -> *)
(*         linkable_mains (prog_main prog1) (prog_main prog2) -> *)
(* *) *)
(*         linkable_programs prog1 prog2. *)

  (* RB: TODO *)
  Theorem linkability_disjoint_procedures :
    forall prog1 prog2,
      well_formed_program prog1 ->
      well_formed_program prog2 ->
      linkable (prog_interface prog1) (prog_interface prog2) ->
      fdisjoint (domm (prog_procedures prog1)) (domm (prog_procedures prog2)).
  Admitted.

  (* RB: TODO *)
  Theorem linkability_disjoint_buffers :
    forall prog1 prog2,
      well_formed_program prog1 ->
      well_formed_program prog2 ->
      linkable (prog_interface prog1) (prog_interface prog2) ->
      fdisjoint (domm (prog_buffers prog1)) (domm (prog_buffers prog2)).
  Admitted.

  (* RB: TODO *)
  Theorem linkability_disjoint_mains :
    forall prog1 prog2,
      well_formed_program prog1 ->
      well_formed_program prog2 ->
      linkable (prog_interface prog1) (prog_interface prog2) ->
      linkable_mains (prog_main prog1) (prog_main prog2).
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
  Admitted.
  (* TODO XXX
    case=> wf1 wf2 sound_int dis_ints dis_procs dis_bufs mainsP C CI.
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
  *)

  Lemma linkable_programs_find_procedure p1 p2 :
    linkable (prog_interface p1) (prog_interface p2) ->
    forall C P Pexpr,
      find_procedure (unionm (prog_procedures p1) (prog_procedures p2)) C P = Some Pexpr
      <-> find_procedure (prog_procedures p1) C P = Some Pexpr
          \/ find_procedure (prog_procedures p2) C P = Some Pexpr.
  Proof.
  Admitted.
  (* TODO XXX
    move=> [_ _ _ _ dis _ _] C P Pexpr.
    move/fdisjointP/(_ C)/implyP: dis.
    rewrite /find_procedure unionmE !mem_domm.
    case p1_C: (prog_procedures p1 C)=> [Cprocs|] //=.
    - by case: (prog_procedures p2 C)=> // _; intuition congruence.
    - by intuition congruence.
  Qed.
  *)

  Lemma linkable_programs_find_procedure_dom p1 p2 :
    linkable (prog_interface p1) (prog_interface p2) ->
    forall C P,
      find_procedure (unionm (prog_procedures p1) (prog_procedures p2)) C P
      = find_procedure (prog_procedures p1) C P
        || find_procedure (prog_procedures p2) C P :> bool.
  Proof.
  Admitted.
  (* TODO XXX
    move=> [_ _ _ _ dis _ _] C P.
    move/fdisjointP/(_ C)/implyP: dis.
    rewrite /find_procedure unionmE !mem_domm.
    case p1_C: (prog_procedures p1 C)=> [Cprocs|] //=.
    by rewrite orbC; case: (prog_procedures p2 C)=> // _.
  Qed.
  *)

  Lemma link_imported_procedure p1 p2 :
    linkable (prog_interface p1) (prog_interface p2) ->
    forall C C' P,
      imported_procedure (unionm (prog_interface p1) (prog_interface p2)) C C' P
      <-> imported_procedure (prog_interface p1) C C' P
          \/ imported_procedure (prog_interface p2) C C' P.
  Proof.
    move=> linkable C C' P.
    rewrite /imported_procedure /Program.has_component /Component.is_importing.
    rewrite unionmE; split.
    - case=> CI [].
      case p1_C: (prog_interface p1 C)=> [CI'|] //=; by eauto.
    - case => [[CI [get_CI in_CI]]|[CI [get_CI in_CI]]].
        by rewrite get_CI /=; eauto.
      (* TODO XXX
      case: linkable=> _ _ _ dis _ _ _.
      move: dis; rewrite fdisjointC=> /fdisjointP/(_ C).
      rewrite !mem_domm get_CI => /(_ erefl).
      by case: (prog_interface p1 C)=> [|] //=; eauto.
  Qed.
  *)
  Admitted.

  Theorem linking_well_formedness:
    forall p1 p2,
      linkable (prog_interface p1) (prog_interface p2) ->
      well_formed_program (program_link p1 p2).
  Proof.
  Admitted.
  (* TODO XXX
    move=> p1 p2 linkable.
    split; try by case: linkable.
    - by case: linkable => *; rewrite !domm_union fsetUSS // wfprog_well_formed_procedures_1.
    - move=> C P [CI []].
      rewrite (linkable_programs_has_component linkable) /= => has_C_CI exp_CI_P.
      rewrite linkable_programs_find_procedure_dom //; apply/orP.
      case: linkable=> wf1 wf2 _ _ _ _ _.
      by case: has_C_CI=> [H|H]; [left|right];
      apply: wfprog_exported_procedures_existence=> //; exists CI; eauto.
    - move=> C P Pexpr.
      rewrite /= (linkable_programs_find_procedure linkable) => find.
      have {find} wf: well_formed_expr p1 C Pexpr \/ well_formed_expr p2 C Pexpr.
        case: find=> [H|H]; [left|right];
        apply: wfprog_well_formed_procedures_2; by case: linkable; eauto.
      split=> /=; last by case: wf=> [[]|[]].
      without loss {linkable wf} [linkable [wf _]]:
        p1 p2 / linkable_programs p1 p2 /\ well_formed_expr p1 C Pexpr.
        case: wf=> wf; eauto; case: (linkable)=> _ _ _ dis1 dis2 _ _.
        rewrite (unionmC dis1) (unionmC dis2); apply.
        by split=> //; apply: linkable_sym.
      move=> /= C' P' /wf {wf}; case: ifP => _.
      + by rewrite linkable_programs_find_procedure_dom // => ->.
      + by rewrite link_imported_procedure //; eauto.
    - rewrite /has_required_local_buffers /= => C.
      case: linkable=> /wfprog_buffers_existence wf1 /wfprog_buffers_existence wf2 _ _ _ dis _.
      rewrite domm_union in_fsetU; case/orP; last rewrite unionmC //; rewrite unionmE.
        by case/wf1=> [[? [->]]|[? [->]]] /=; eauto.
      by case/wf2=> [[? [->]]|[? [->]]] /=; eauto.
    - move=> mainC mainP; rewrite /= /main_link /=.
      case: (linkable)=> wf1 wf2 _ _ _ _; rewrite /linkable_mains.
      rewrite linkable_programs_find_procedure_dom //.
      case Hp1: (prog_main p1)=> [main|] //=.
        by move=> _ [?]; subst main; rewrite (wfprog_main_existence wf1).
      by move=> ??; rewrite (wfprog_main_existence wf2) ?orbT.
  Qed.
  *)

  Lemma linked_programs_main_component_origin:
    forall p1 p2,
      linkable (prog_interface p1) (prog_interface p2) ->
      closed_program (program_link p1 p2) ->
      main_comp (program_link p1 p2) \in domm (prog_interface p1) \/
      main_comp (program_link p1 p2) \in domm (prog_interface p2).
  Proof.
  (* TODO XXX
    intros p1 p2.
    intros Hlink Hclosed.
    apply cprog_main_existence in Hclosed.
    unfold main_comp.
    destruct Hclosed as [mainC [mainP [main_procs [Hmain_C_P [Hprocs Hproc_P]]]]].
    rewrite Hmain_C_P.
    unfold program_link in Hprocs. simpl in *.
    rewrite unionmE in Hprocs.
    destruct ((prog_procedures p1) mainC) eqn:Hmain_in_p1.
    + rewrite Hmain_in_p1 in Hprocs. simpl in *.
      inversion Hprocs. subst.
      left.
      inversion Hlink.
      apply wfprog_well_formed_procedures_1 in H.
      (* subset stuff *)
      admit.
    + rewrite Hmain_in_p1 in Hprocs. simpl in *.
      inversion Hprocs. subst.
      right.
      inversion Hlink.
      apply wfprog_well_formed_procedures_1 in H1.
      (* subset stuff *)
      admit.
  *)
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
      linkable (prog_interface p1) (prog_interface p2) ->
    forall C b,
      (prepare_buffers (program_link p1 p2)).2 C = Some b ->
      C \notin domm (prog_interface p2) ->
      C \in domm (prog_interface p1) /\ (prepare_buffers p1).2 C = Some b.
  Proof.
  Admitted.

  Lemma find_procedure_in_linked_programs:
    forall p1 p2,
      linkable (prog_interface p1) (prog_interface p2) ->
    forall C P P_expr,
      find_procedure (unionm (prog_procedures p1) (prog_procedures p2)) C P = Some P_expr ->
      C \notin domm (prog_interface p2) ->
      C \in domm (prog_interface p1) /\ find_procedure (prog_procedures p1) C P = Some P_expr.
  Proof.
  Admitted.
End Source.

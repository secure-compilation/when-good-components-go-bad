Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From extructures Require Import ord fset fmap.

Local Open Scope fset_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* Pondering : E_seq (e1) (E_seq e2 e3) should be the same as E_seq (E_seq e1 e2) e3 *)
(* or more more naturally : e1; (e2; e3) = (e1; e2); e3 *)
(* sequence should be associative ?*)
(* or maybe we just stick to one of the representation since this could
   complicate things in the semantics / during the compilaiton *)
Inductive expr : Type :=
| E_val : value -> expr
| E_arg : expr
| E_local : Block.buffer_kind -> expr
| E_binop : binop -> expr -> expr -> expr
| E_seq : expr -> expr -> expr
| E_if : expr -> expr -> expr -> expr
| E_alloc : expr -> expr
| E_deref : expr -> expr
| E_assign : expr -> expr -> expr
| E_call : Component.id -> Procedure.id -> expr -> expr
| E_component_buf : Component.id -> expr
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

  (* maybe move it elsewhere *)
  Definition component_buffers : Type
    := buffer * buffer.

  Record program : Type := mkProg {
    prog_interface : Program.interface;
    prog_procedures : NMap (NMap expr);
    (* public and private *)
    prog_buffers : NMap component_buffers
  }.

  (* maybe not really useful *)
  (* but allows us to abstract the buffer*buffer type at some extent *)
  Definition get_buffer_with_id
             (prog:program)
             (cid:Component.id)
             (bk:Block.buffer_kind) : option buffer :=
    match (prog_buffers prog) cid with
    | Some comp_bufs =>
      match bk with
      | Block.pub  => Some (fst comp_bufs)
      | Block.priv => Some (snd comp_bufs)
      end
    | None => None
    end.

  Definition get_buffer
             (comp_bufs:component_buffers)
             bk : buffer :=
    match bk with
    | Block.pub  => fst comp_bufs
    | Block.priv => snd comp_bufs
    end.

  (* maybe use something like converting the component_buffers to a
  list/map for when we use both of them (would be better than
  selecting one then the other since it's used repeatedly *)
  Definition get_buffers_as_map (comp_bufs:component_buffers) :=
    let '(pub, priv) := comp_bufs in
    mkfmap [(Block.public, pub); (Block.private, priv)].

  (** Lookup definition of procedure [C.P] in the map [procs]. *)
  Definition find_procedure
             (procs: NMap (NMap expr))
             (C: Component.id) (P: Procedure.id) : option expr :=
    match procs C with
    | Some C_procs => C_procs P
    | None         => None
    end.

  Definition prog_main (p : program) : option expr :=
    find_procedure (prog_procedures p) Component.main Procedure.main.

  Definition valid_calls
             (procs: NMap (NMap expr))
             (intf: Program.interface)
             (cur_comp: Component.id)
             (calls: {fset Component.id * Procedure.id}) :=
    forall C P, (C, P) \in calls ->
      if C == cur_comp then find_procedure procs cur_comp P : Prop
      else imported_procedure intf cur_comp C P.

  (* a program has valid buffers if the sizes in the components interfaces is
     the same as the one of the statically allocated public buffers *)
 Definition valid_buffers
            (prog : program) :=
   mapm (fun (comp_bufs : component_buffers) =>
           buffer_size (get_buffer comp_bufs Block.pub)) (prog_buffers prog) =
    mapm (fun comp_intf => Component.public_buffer_size comp_intf) (prog_interface prog).

  Fixpoint values_are_integers (e: expr) : bool :=
    match e with
    | E_val (Int _)     => true
    | E_val _           => false
    | E_arg             => true
    | E_local _         => true
    | E_exit            => true
    | E_binop _ e1 e2   => values_are_integers e1 && values_are_integers e2
    | E_seq     e1 e2   => values_are_integers e1 && values_are_integers e2
    | E_if   e1 e2 e3   => [&& values_are_integers e1, values_are_integers e2 &
                             values_are_integers e3]
    | E_alloc e         => values_are_integers e
    | E_deref e         => values_are_integers e
    | E_assign  e1 e2   => values_are_integers e1 && values_are_integers e2
    | E_call   _ _ e    => values_are_integers e
    | E_component_buf _ => true
    end.

  (* An expression is well-formed when:
     1) calls outside the component are allowed by the interface
     2) calls inside the component are targeting existing procedures
     3) the undef value is not present
     4) pointers are not present (no pointer forging) *)
  Definition well_formed_expr (p: program) (cur_comp: Component.id) (e: expr) : Prop :=
    valid_calls (prog_procedures p) (prog_interface p) cur_comp (called_procedures e)
    (* /\ valid_static_access p cur_com e *)
    /\ values_are_integers e.

  (* Component C has a private buffer of size at least one *)
  (* used for the counter during back-translation *)
  Definition has_required_local_buffers (p: program) (C: Component.id) : Prop :=
    exists2 bufs,
      prog_buffers p C = Some bufs &
      let '(pub, priv) := bufs in
        (* (buffer_size pub) > 0 /\ *) (buffer_size priv) > 0.

  Record well_formed_program (p: program) := {
    (* the interface is sound (but maybe not closed) *)
    wfprog_interface_soundness:
      sound_interface (prog_interface p);
    (* there are procedures only for the declared components *)
    wfprog_defined_procedures: domm (prog_interface p) = domm (prog_procedures p);
    (* each exported procedure is actually defined *)
    wfprog_exported_procedures_existence:
      forall C P, exported_procedure (prog_interface p) C P ->
      find_procedure (prog_procedures p) C P;
    (* each instruction of each procedure is well-formed *)
    wfprog_well_formed_procedures:
      forall C P Pexpr,
        find_procedure (prog_procedures p) C P = Some Pexpr ->
        well_formed_expr p C Pexpr;
    (* each declared component has the required static buffers *)

    (* FG : shouldn't this evidence go along with well formed buffers ? *)
    wfprog_defined_buffers: domm (prog_interface p) = domm (prog_buffers p);
    (* each component's buffer is well formed *)
    wfprog_well_formed_buffers:
      valid_buffers p /\
      forall C, prog_interface p C ->
           has_required_local_buffers p C;
    (* if the main component is defined, so is the main procedure *)
    wfprog_main_existence:
      Component.main \in domm (prog_interface p) -> prog_main p;
  }.

  (* a closed program is a program with a closed interface and an existing main
     procedure *)
  Record closed_program (p: program) := {
    (* the interface must be closed (and consequently sound) *)
    cprog_closed_interface:
      closed_interface (prog_interface p);
    (* the main procedure must exist *)
    cprog_main_existence: prog_main p
  }.

  Theorem linkable_disjoint_procedures :
    forall prog1 prog2,
      well_formed_program prog1 ->
      well_formed_program prog2 ->
      linkable (prog_interface prog1) (prog_interface prog2) ->
      fdisjoint (domm (prog_procedures prog1)) (domm (prog_procedures prog2)).
  Proof.
    move=> p1 p2 wf1 wf2 [sound_intf dis].
    by rewrite -(wfprog_defined_procedures wf1) -(wfprog_defined_procedures wf2).
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

  Definition linkable_mains (prog1 prog2 : program) : Prop :=
    ~~ (prog_main prog1 && prog_main prog2).

  Lemma linkable_disjoint_mains :
    forall prog1 prog2,
      well_formed_program prog1 ->
      well_formed_program prog2 ->
      linkable (prog_interface prog1) (prog_interface prog2) ->
      linkable_mains prog1 prog2.
  Proof.
    rewrite /linkable_mains /prog_main /find_procedure.
    move=> p1 p2 Hwf1 Hwf2 [_ /fdisjointP/(_ Component.main)/implyP].
    rewrite (wfprog_defined_procedures Hwf1) (wfprog_defined_procedures Hwf2) !mem_domm.
    case: (prog_procedures p1 Component.main)=> [C_procs|] //=.
    by case: (prog_procedures p2 Component.main)=> //=; rewrite andbF.
  Qed.

  Lemma linkable_mains_sym :
    forall prog1 prog2,
      linkable_mains prog1 prog2 ->
      linkable_mains prog2 prog1.
  Proof. by rewrite /linkable_mains=> p1 p2; rewrite andbC. Qed.

  Definition program_link (p1 p2: program) : program :=
    {| prog_interface := unionm (prog_interface p1) (prog_interface p2);
       prog_procedures := unionm (prog_procedures p1) (prog_procedures p2);
       prog_buffers := unionm (prog_buffers p1) (prog_buffers p2) |}.

  Lemma link_sym: forall p1 p2,
    well_formed_program p1 ->
    well_formed_program p2 ->
    linkable (prog_interface p1) (prog_interface p2) ->
    program_link p1 p2 = program_link p2 p1.
  Proof.
    move=> p1 p2 wf1 wf2 l12; rewrite /program_link.
    congr mkProg; apply: unionmC.
    - by case: l12.
    - by apply: linkable_disjoint_procedures.
    - by apply: linkable_disjoint_buffers.
  Qed.

  Definition program_unlink (Cs: {fset Component.id}) (p: program) : program :=
    {| prog_interface  := filterm (fun C _ => C \in Cs) (prog_interface p);
       prog_procedures := filterm (fun C _ => C \in Cs) (prog_procedures p);
       prog_buffers    := filterm (fun C _ => C \in Cs) (prog_buffers p) |}.

  Lemma program_linkKL p1 p2 :
    well_formed_program p1 ->
    well_formed_program p2 ->
    linkable (prog_interface p1) (prog_interface p2) ->
    program_unlink (domm (prog_interface p1)) (program_link p1 p2) = p1.
  Proof.
    case: p1 p2 => [i1 p1 b1] [i2 p2 b2] wf1 wf2 l12.
    rewrite /program_unlink /program_link /=; congr mkProg.
    - by rewrite -[RHS](unionmK i1 i2); apply/eq_filterm=> ??; rewrite mem_domm.
    - rewrite -[RHS](unionmK p1 p2); apply/eq_filterm=> ??.
      by rewrite (wfprog_defined_procedures wf1) /= mem_domm.
    - rewrite -[RHS](unionmK b1 b2); apply/eq_filterm=> ??.
      by rewrite (wfprog_defined_buffers wf1) /= mem_domm.
  Qed.

  Lemma program_linkKR p1 p2 :
    well_formed_program p1 ->
    well_formed_program p2 ->
    linkable (prog_interface p1) (prog_interface p2) ->
    program_unlink (domm (prog_interface p2)) (program_link p1 p2) = p2.
  Proof.
    move=> wf1 wf2 l12.
    rewrite link_sym // program_linkKL //.
    exact: linkable_sym.
  Qed.

  Lemma program_unlinkK i1 i2 p :
    prog_interface p = unionm i1 i2 ->
    well_formed_program p ->
    linkable i1 i2 ->
    program_link (program_unlink (domm i1) p) (program_unlink (domm i2) p) = p.
  Proof.
    case: p => _ pp pb /= -> Hwf [Hsound Hdis]; rewrite /program_link /=.
    congr mkProg.
    - apply/eq_fmap=> /= C; move/fdisjointP/(_ C)/implyP: Hdis.
      rewrite !unionmE !filtermE !unionmE !mem_domm.
      by case: (i1 C) (i2 C) => [?|] //= [?|] //=.
    - apply/eq_fmap=> /= C; move/fdisjointP/(_ C)/implyP: Hdis.
      move/wfprog_defined_procedures/eq_fset/(_ C): Hwf => /=.
      rewrite !unionmE !filtermE !mem_domm !unionmE.
      by case: (pp C) (i1 C)=> [?|] //= [?|] //= ->.
    - apply/eq_fmap=> /= C; move/fdisjointP/(_ C)/implyP: Hdis.
      move/wfprog_defined_buffers/eq_fset/(_ C): Hwf => /=.
      rewrite !unionmE !filtermE !mem_domm !unionmE.
      by case: (pb C) (i1 C)=> [?|] //= [?|] //= ->.
  Qed.

  Lemma exported_procedure_filter_comp i (f : nat -> bool) C P :
    exported_procedure (filterm (fun C' _ => f C') i) C P
    <-> f C /\ exported_procedure i C P.
  Proof.
    rewrite /exported_procedure /Program.has_component /Component.is_exporting.
    split.
    - case=> CI []; rewrite !filtermE.
      by case: (i C) (f C)=> [_|] //= [] //= [->]; eauto.
    - case=> f_C [CI [i_C P_CI]].
      by exists CI; rewrite filtermE i_C /= f_C.
  Qed.

  Lemma imported_procedure_filter_comp i (f : nat -> bool) C C' P :
    imported_procedure (filterm (fun C _ => f C) i) C C' P
    <-> f C /\ imported_procedure i C C' P.
  Proof.
    rewrite /imported_procedure /Program.has_component /Component.is_importing.
    split.
    - case=> CI []; rewrite !filtermE.
      by case: (i C) (f C)=> [_|] //= [] //= [->]; eauto.
    - case=> f_C [CI [i_C C'_P_CI]].
      by exists CI; rewrite filtermE i_C /= f_C.
  Qed.

  Lemma find_procedure_filter_comp procs (f : nat -> bool) C P :
    find_procedure (filterm (fun C' _ => f C') procs) C P =
    if f C then find_procedure procs C P else None.
  Proof.
    rewrite /find_procedure filtermE.
    by case: (procs C) (f C)=> [?|] //= [].
  Qed.

  Lemma well_formed_program_unlink Cs p :
    well_formed_program p ->
    well_formed_program (program_unlink Cs p).
  Proof.
    case: p => [pi pp pb] wf; split=> /=.
    - (* interface soundness *)
      move=> C C' P [CI []].
      rewrite /Program.has_component /Component.is_importing /Component.is_exporting.
      rewrite !filtermE.
      case pi_C: (pi C)=> [CI'|] //= HCI.
      case: ifP HCI pi_C=> [C_Cs|] //  [->] {CI'} pi_C C'_P CI'.
      have Himp : imported_procedure pi C C' P by exists CI; split.
      move/wfprog_interface_soundness/(_ _ _ _ Himp CI'): wf.
      rewrite /Program.has_component /=.
      case pi_C': (pi C')=> [CI''|] //=.
        by case: ifP.
    - (* defined procedures *)
      apply/eq_fset=> C; move/wfprog_defined_procedures/eq_fset/(_ C): wf.
      rewrite /= !mem_domm !filtermE.
      by case: (pp C) (pi C) (C \in Cs) => [?|] //= [?|] //= [].
    - (* exported procedures existence *)
      move=> C P.
      rewrite exported_procedure_filter_comp find_procedure_filter_comp.
      case=> ->.
      exact: (wfprog_exported_procedures_existence wf).
    - (* well formed procedures *)
      move=> C P Pexpr; rewrite find_procedure_filter_comp.
      case: ifP=> //= C_Cs pp_C_P.
      case/wfprog_well_formed_procedures/(_ _ _ _ pp_C_P): wf=> /= Hcalls Hints.
      split=> //= C' P' /Hcalls.
      rewrite find_procedure_filter_comp C_Cs.
      case: ifP=> // _.
      by rewrite imported_procedure_filter_comp.
    - (* defined buffers *)
      apply/eq_fset=> C; move/wfprog_defined_buffers/eq_fset/(_ C): wf.
      rewrite /= !mem_domm !filtermE.
      by case: (pb C) (pi C) (C \in Cs) => [?|] //= [?|] //= [].
    - (* well formed buffers *)
      split.
      + admit.
      + move=> C; rewrite filtermE.
        case pi_C: (pi C)=> [CI|] //=.
        case: ifP=> //= C_Cs _.

        (* move/wfprog_well_formed_buffers/(_ C): wf=> /=. *)
        (* rewrite pi_C=> /(_ erefl) [bufs /= pb_C ?]. *)
        (*   by exists bufs => //=; rewrite filtermE pb_C /= C_Cs. *)
        admit.

    - (* main existence *)
      have /= /implyP := wfprog_main_existence wf.
      rewrite /prog_main /find_procedure !mem_domm !filtermE.
      have : pi Component.main = pp Component.main :> bool.
        by rewrite -!mem_domm (wfprog_defined_procedures wf).
      case: (pi Component.main)=> [CI|] //=.
      case: (pp Component.main)=> [C_procs|] //= _.
      by case: (Component.main \in Cs).
  Admitted.

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
    - by case: link => *; rewrite !domm_union // !wfprog_defined_procedures.
    - move=> C P [CI []].
      rewrite (linkable_programs_has_component link) /= => has_C_CI exp_CI_P.
      rewrite linkable_programs_find_procedure_dom //; apply/orP.
      by case: has_C_CI=> [H|H]; [left|right];
      apply: wfprog_exported_procedures_existence=> //; exists CI; eauto.
    - move=> C P Pexpr.
      rewrite /= (linkable_programs_find_procedure wf1 wf2 link) => find.
      have {find} wf: well_formed_expr p1 C Pexpr \/ well_formed_expr p2 C Pexpr.
        case: find=> [H|H]; [left|right];
        apply: wfprog_well_formed_procedures; by case: link; eauto.
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
    - split.
      + admit.
      + rewrite /has_required_local_buffers /= => C.
        move: (linkable_disjoint_buffers wf1 wf2 link)=> dis_buf.
        move/wfprog_well_formed_buffers in wf1.
        move/wfprog_well_formed_buffers in wf2.
        destruct wf1 as [_ wf1'].
        destruct wf2 as [_ wf2'].
        rewrite -mem_domm domm_union in_fsetU ; case/orP; last rewrite unionmC //; rewrite unionmE.
          rewrite mem_domm ; case/wf1'=> [? ->] /=; eauto.
            by rewrite mem_domm; case/wf2'=> [? ->] /=; eauto.
    - have /implyP := wfprog_main_existence wf1.
      have /implyP := wfprog_main_existence wf2.
      rewrite /= /prog_main /find_procedure !mem_domm !unionmE.
      rewrite -[isSome (prog_procedures p1 Component.main)]mem_domm.
      rewrite -(wfprog_defined_procedures wf1) mem_domm.
      case: (prog_interface p1 Component.main)=> [CI|] //=.
      by case: (prog_interface p2 Component.main)=> [CI|] //=.
  Admitted.

  Lemma linked_programs_main_component_origin:
    forall p1 p2,
      well_formed_program p1 ->
      well_formed_program p2 ->
      linkable (prog_interface p1) (prog_interface p2) ->
      closed_program (program_link p1 p2) ->
      Component.main \in domm (prog_interface p1) \/
      Component.main \in domm (prog_interface p2).
  Proof.
    move=> p1 p2 wf1 wf2 [_ Hdis] Hclosed.
    have := cprog_main_existence Hclosed.
    rewrite /prog_main /find_procedure /= unionmE -!mem_domm.
    rewrite !wfprog_defined_procedures // !mem_domm.
    case: (prog_procedures p1 Component.main)=> [main_procs'|] //=; eauto.
    by case: (prog_procedures p2 Component.main)=> [main_procs'|] //=; eauto.
  Qed.

  Lemma interface_preserves_closedness_l p1 p2 p1' :
    closed_program (program_link p1 p2) ->
    prog_interface p1 = prog_interface p1' ->
    well_formed_program p1 ->
    well_formed_program p1' ->
    closed_program (program_link p1' p2).
  Proof.
    move=> [H1 H2] Hint wf1 wf1'; split; first by rewrite /= -Hint.
    move/implyP: (wfprog_main_existence wf1).
    move/implyP: (wfprog_main_existence wf1').
    move: H2; rewrite /prog_main /find_procedure /= !unionmE -!mem_domm.
    rewrite -(wfprog_defined_procedures wf1') -Hint (wfprog_defined_procedures wf1).
    by case: ifP=> //=.
  Qed.

  Lemma closed_program_link_sym p1 p2 :
    well_formed_program p1 ->
    well_formed_program p2 ->
    linkable (prog_interface p1) (prog_interface p2) ->
    closed_program (program_link p1 p2) = closed_program (program_link p2 p1).
  Proof.
    intros Hwf1 Hwf2 Hlinkable.
    rewrite (link_sym Hwf1 Hwf2 Hlinkable).
    reflexivity.
  Qed.

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

  (* Prealloc the public part and the private part "flatly" *)
  Definition prepare_buffers (p: program) : Memory.t :=
    mapm (fun bufs =>
            ComponentMemory.prealloc (get_buffers_as_map bufs))
         (prog_buffers p).

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
    rewrite linkable_programs_find_procedure // /find_procedure.
    rewrite !wfprog_defined_procedures //.
    rewrite !mem_domm; case.
    - by case: (prog_procedures p1 C); eauto.
    - by case: (prog_procedures p2 C)=> [C_procs /=|] //= _.
  Qed.

  Lemma find_procedure_unionm_r : forall (procs1 procs2 : NMap (NMap expr)) cid pid proc,
    find_procedure (unionm procs1 procs2) cid pid = Some proc ->
    cid \in domm procs1 = false ->
    find_procedure procs2 cid pid = Some proc.
  Proof.
    intros procs1 procs2 cid pid proc Hfind Hnotin.
    unfold find_procedure in Hfind.
    rewrite unionmE in Hfind.
    rewrite mem_domm in Hnotin.
    rewrite Hnotin in Hfind.
    destruct (procs2 cid) as [C_procs |] eqn:Hprocs;
      rewrite Hprocs in Hfind.
    - unfold find_procedure.
      by rewrite Hprocs.
    - by inversion Hfind.
  Qed.

End Source.

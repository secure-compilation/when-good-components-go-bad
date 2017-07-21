Require Import Smallstep.
Require Import Behavior.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.

(* 
   Full proof of robust compilation relying on 
   - target decomposition,
   - compiler correctness and 
   - source definability
 *)

(* 
   Some Global definitions.
 *)

(* Component id *)
Axiom id : Type.
Definition interface := list id.
(* check if the last event of a behavior belongs to an agent,
   represented by the interface of its components *)
Axiom turn : program_behavior -> interface -> Prop.
(* check if an interface is complete *)
Axiom icomplete : interface -> Prop.
(* check if the union of two interfaces is complete *)
Definition icomplete2 (i1 i2:interface) := icomplete (i1++i2).
(* TODO check this *)
Axiom unique_interfaces :
  forall (i1 i2 i3:interface),
    icomplete2 i1 i3 -> icomplete2 i2 i3 -> i1=i2.

(* 
   option monad stuff
 *)
Definition map {A B} (f: A -> B) (o: option A) : option B :=
  match o with
  | Some a => Some (f a)
  | None => None
  end.

Definition map_compose :
  forall {A B C} (f1: A -> B) (f2: B -> C) (x:option A),
    map f2 (map f1 x) = map (compose f2 f1) x.
Proof.
  destruct x; auto.
Qed.

Definition behaves (o: option semantics) b :=
    match o with
    | Some p => program_behaves p b
    | None => False
    end.


(* 
   The languages.
 *)

(* Signature of basic things expected in a language *)
Module Type Lang.
  (* Type of programs, complete or partial *)
  Axiom program : Type.
  Axiom get_interface: program -> interface.
  (* checks if a program has a complete interface *)
  Axiom complete: program -> Prop.
  (* checks if two programs linked together form a complete program *)
  Axiom complete2: program -> program -> Prop.

  (* complete semantics: takes a complete program *)
  Axiom sem: option program -> option semantics.
  (* Axiom sem_complete: *)
  (*   forall (p:program), *)
  (*     complete p -> exists s, sem (Some p) = Some s. *)

  (* partial semantics: takes a program and a matching interface.
     The interface of the program together with the matching interface
     is complete. *)
  Axiom psem: option program -> interface -> option semantics.
  (* Axiom psem_complete: *)
  (*   forall psi (p:program), *)
  (*     icomplete2 psi (get_interface p) -> exists s, psem (Some p) psi = Some s. *)
  (* Axiom idefinability: forall (i:interface), exists (p:program), get_interface p = i. *)
End Lang.

(* Every language is a subtype of Lang and implements its signature *)
(* Note: nothing is really implemented, we just give type signatures *)

(* Target *)
Module T <: Lang.
  Axiom program : Type.
  Axiom get_interface: program -> interface.
  Definition complete (p:program) := icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := icomplete2 (get_interface p1) (get_interface p2).
  Axiom sem: option program -> option semantics.
  Axiom psem: option program -> interface -> option semantics.

  (* takes a complete program and produces a partial one
   This is an important ingredient for the simulation relation.
   For MP the relation corresponds with this function actually.
   For SFI the relation contains additional elements.
   *)
  Axiom partialize: interface -> T.program -> T.program.
  (* Axiom partialize_post: *)
  (*   forall (p pp:T.program) psi, *)
  (*   partialize psi p = pp -> *)
  (*   (T.get_interface p) = (T.get_interface pp)++psi. *)
End T.

(* Intermediate *)
Module I <: Lang.
  Axiom program : Type.
  Axiom get_interface: program -> interface.
  Definition complete (p:program) := icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := icomplete2 (get_interface p1) (get_interface p2).
  Axiom sem: option program -> option semantics.
  Axiom psem: option program -> interface -> option semantics.

  (* linking of two partial programs, returns a complete program *)
  Axiom link: program -> program -> option program.
  Axiom link_prepost:
    forall (p1 p2:program),
      complete2 p1 p2 -> exists p, (link p1 p2 = Some p) /\ (get_interface p = (get_interface p1) ++ (get_interface p2)).

  Axiom decomposition:
    forall beh (c p:I.program),
      behaves (I.sem (I.link c p)) beh
      ->
      behaves (I.psem (Some p) (I.get_interface c)) beh.

  Definition fully_defined (psi:interface) (p:program) :=
    forall (beh:program_behavior) (c:program),
      get_interface c = psi ->
      complete2 c p ->
      behaves (sem (link c p)) beh ->
      (turn beh (get_interface p) ->
      not_wrong beh).
End I.

(* Source *)
Module S <: Lang.
  Axiom program : Type.
  Axiom get_interface: program -> interface.
  Definition complete (p:program) := icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := icomplete2 (get_interface p1) (get_interface p2).
  Axiom sem: option program -> option semantics.
  Axiom psem: option program -> interface -> option semantics.

  Axiom link: program -> program -> option program.

  Definition fully_defined (psi:interface) (p:program) :=
    forall (beh:program_behavior) (c:program),
      get_interface c = psi ->
      complete2 c p ->
      behaves (sem (link c p)) beh ->
      (turn beh (get_interface p) ->
      not_wrong beh).

  Axiom definability:
    forall (beh:program_behavior) (psi:interface) (p:program),
      icomplete2 psi (get_interface p) ->
      behaves (psem (Some p) psi) beh ->
      exists (c:program),
        behaves (sem (link c p)) beh /\ get_interface c = psi.
End S.


(* This module takes a high language L1 and a low one L2 and produces
   a compiler from L1 to L2 and some properties *)
Module Compiler (L1 L2: Lang).
  Axiom compile : L1.program -> L2.program.
  Axiom compile_complete :
    forall p1 p2,
      L1.complete p1 -> compile p1 = p2 -> L2.complete p2.
  
  Axiom compiler_interfaces:
  forall (p1:L1.program),
    L1.get_interface p1 = L2.get_interface (compile p1).
End Compiler.

Module IT := Compiler I T.
Module SI := Compiler S I.

(* TODO IT.compile must be a refinement compiler *)

(* exact cc preserves also UB *)
Axiom SIcompiler_correctness :
  forall beh (p:S.program) (psi:interface),
    behaves (I.psem (Some (SI.compile p)) psi) beh ->
    behaves (S.psem (Some p) psi) beh.


(* Warm-up: RC between S and I *)
Definition SIrc:
  forall (c:I.program) (P:S.program) (beh:program_behavior),
    icomplete2 (I.get_interface c) (S.get_interface P) ->
    S.fully_defined (I.get_interface c) P ->
    behaves (I.sem (I.link c (SI.compile P))) beh
    ->
    exists C,
      behaves (S.sem (S.link C P)) beh /\ S.complete2 C P.
Proof.
  intros c P b Hcomplete SFD H.
  apply I.decomposition in H.
  destruct (I.link_prepost c (SI.compile P)) as [p [H1 H2]].
  unfold I.complete2.
  rewrite <- SI.compiler_interfaces.
  auto.
  apply (SIcompiler_correctness b P (I.get_interface c)) in H.
  apply S.definability in H.
  destruct H as [C [Hb Hif]].
  exists C.
  split.
  auto.
  rewrite <- Hif in Hcomplete.
  auto.
  auto.
Qed.



(* 
   We now got for RC between S and T.
   The following properties are special because they depend on
   compiling the complete intermediate program.
 *)
Axiom Tspecial_decomposition:
  forall beh (c p:I.program),
    I.fully_defined (I.get_interface c) p ->
    let ip := map IT.compile (I.link c p) in
    behaves (T.sem ip) beh
    ->
    behaves (T.psem (map (T.partialize (I.get_interface c)) ip) (I.get_interface c)) beh.

Axiom ITspecial_compiler_correctness:
  forall beh (c p:I.program),
    I.fully_defined (I.get_interface c) p ->
    let ip := I.link c p in
    let tp := map (T.partialize (I.get_interface c)) (map IT.compile ip) in
    behaves (T.psem tp (I.get_interface c)) beh ->
    behaves (I.psem (Some p) (I.get_interface c)) beh.

(* This is proved using SIrc. *)
Definition FD_preservation:
  forall (psi:interface) (p:S.program),
  S.fully_defined psi p ->
  I.fully_defined psi (SI.compile p).
Proof.
  intros psi p SFD.
  intros b c Hpsi Hcomplete H1.
  unfold I.complete2 in Hcomplete.
  rewrite <- SI.compiler_interfaces in Hcomplete.
  destruct (SIrc c p b Hcomplete) as [C [H2 H3]].
  rewrite Hpsi.
  apply SFD.
assumption.
  unfold S.fully_defined in SFD.
  rewrite <- SI.compiler_interfaces.
  apply (SFD b C).
  unfold S.complete2 in H3.  
  destruct (unique_interfaces (I.get_interface c) (S.get_interface C) (S.get_interface p)); auto.
auto.
auto.
Qed.

(* 
   This property is different from the one we started from: there is
   no concept of linking at the low level.
   A program is composed at the intermediate, compiled as a complete
   program and run at the target.
   Instead of linking to partial target programs, we go to the partial
   semantics by partializing a complete target program.
 *)

Definition robust_compilation_static_compromise :=
  forall (c:I.program) (P:S.program) (beh:program_behavior),
    icomplete2 (I.get_interface c) (S.get_interface P) ->
    S.fully_defined (I.get_interface c) P ->
    behaves (T.sem (map IT.compile (I.link c (SI.compile P)))) beh
    ->
    exists C, 
      behaves (S.sem (S.link C P)) beh /\ S.complete2 C P.

Theorem proof_rc_static : robust_compilation_static_compromise.
Proof.
  intros c P b Hcomplete SFD H.
  apply (Tspecial_decomposition b c (SI.compile P)) in H.
  apply ITspecial_compiler_correctness in H.
  destruct (S.definability b (I.get_interface c) P Hcomplete) as [C [H1 Hinterfaces]].
  apply (SIcompiler_correctness b P (I.get_interface c)) in H.
  assumption.
  rewrite <- Hinterfaces in Hcomplete.
  exists C.
  auto.
  apply FD_preservation.
  assumption.
  apply FD_preservation.
  assumption.
Qed.


(* This definition is weaker than the above but has the advantage of
   not mentioning the intermediate language *)
Definition robust_compilation_static_compromise_corollary :=
  forall (Q P:S.program) (beh:program_behavior),
    S.complete2 Q P ->
    S.fully_defined (S.get_interface Q) P ->
    let compile := compose IT.compile SI.compile in
    behaves (T.sem (map compile (S.link Q P))) beh ->
    exists C, behaves (S.sem (S.link C P)) beh /\ S.complete2 C P.

(* TODO This is too syntactic, it should be stated in terms of equivalent behaviors *)
Axiom Sseparate_compilation:
  forall (P Q: S.program),
    map SI.compile (S.link Q P) = I.link (SI.compile Q) (SI.compile P).

Corollary robust_compilation_corrolary :
  robust_compilation_static_compromise ->
  robust_compilation_static_compromise_corollary.
Proof.
  intros RC Q P b Hcompl H1 H2 H3.
  specialize (RC (SI.compile Q) P b).
  rewrite <- SI.compiler_interfaces in RC.
  unfold H2 in H3.
  rewrite <- Sseparate_compilation in RC.
  rewrite <- map_compose in H3.  
  apply (RC Hcompl H1 H3).
Qed.

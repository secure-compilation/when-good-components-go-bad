Require Import Smallstep.
Require Import Behavior.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.

(* 
   Full proof of robust compilation relying on 
   - target decomposition,
   - compiler correctness and 
   - source definability
  
   For a simple instance refer to SI.RC, a more complicate instance is
   in Main.robust_compilation_static_compromise.
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

Definition propagate {A B} (f: A -> option B) (op:option A) : option B :=
  match op with
  | Some p => f p
  | None => None
  end.

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
  Axiom sem: program -> option semantics.
  (* Axiom sem_complete: *)
  (*   forall (p:program), *)
  (*     complete p -> exists s, sem (Some p) = Some s. *)

  (* partial semantics: takes a program and a matching interface.
     The interface of the program together with the matching interface
     is complete. *)
  Axiom psem: interface -> program -> option semantics.
  (* Axiom psem_complete: *)
  (*   forall psi (p:program), *)
  (*     icomplete2 psi (get_interface p) -> exists s, psem (Some p) psi = Some s. *)
  Definition osem (op: option program) := propagate sem op.
  Definition opsem i (op: option program) := propagate (psem i) op.

  (* Axiom idefinability: forall (i:interface), exists (p:program), get_interface p = i. *)
End Lang.

(* Every language is a subtype of Lang and implements its signature *)
(* Note: nothing is really implemented, we just give type signatures *)

(* Intermediate *)
Module I <: Lang.
  Axiom program : Type.
  Axiom get_interface: program -> interface.
  Definition complete (p:program) := icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := icomplete2 (get_interface p1) (get_interface p2).
  Axiom sem: program -> option semantics.
  Axiom psem: interface -> program -> option semantics.
  Definition osem (op: option program) := propagate sem op.
  Definition opsem i (op: option program) := propagate (psem i) op.

  (* linking of two partial programs, returns a complete program *)
  Axiom link: program -> program -> option program.
  Axiom link_prepost:
    forall (p1 p2:program),
      complete2 p1 p2 -> exists p, (link p1 p2 = Some p) /\ (get_interface p = (get_interface p1) ++ (get_interface p2)).

  Axiom decomposition:
    forall beh (c p:I.program),
      behaves (osem (I.link c p)) beh
      ->
      behaves (opsem (I.get_interface c) (Some p)) beh.

  Definition fully_defined (psi:interface) (p:program) :=
    forall (beh:program_behavior) (c:program),
      get_interface c = psi ->
      complete2 c p ->
      behaves (osem (link c p)) beh ->
      (turn beh (get_interface p) ->
       not_wrong beh).
End I.

(* Source *)
Module S <: Lang.
  Axiom program : Type.
  Axiom get_interface: program -> interface.
  Definition complete (p:program) := icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := icomplete2 (get_interface p1) (get_interface p2).
  Axiom sem: program -> option semantics.
  Axiom psem: interface -> program -> option semantics.
  Definition osem (op: option program) := propagate sem op.
  Definition opsem i (op: option program) := propagate (psem i) op.

  Axiom link: program -> program -> option program.

  Definition fully_defined (psi:interface) (p:program) :=
    forall (beh:program_behavior) (c:program),
      get_interface c = psi ->
      complete2 c p ->
      behaves (osem (link c p)) beh ->
      (turn beh (get_interface p) ->
       not_wrong beh).

  Axiom definability:
    forall (beh:program_behavior) (psi:interface) (p:program),
      icomplete2 psi (get_interface p) ->
      behaves (psem psi p) beh ->
      exists (c:program),
        behaves (osem (link c p)) beh /\ get_interface c = psi.
End S.

(* Source to Intermediate *)
Module SI.
  Axiom compile : S.program -> I.program.
  Axiom compile_complete :
    forall p1 p2,
      S.complete p1 -> compile p1 = p2 -> I.complete p2.
  
  Axiom compiler_interfaces:
    forall (p1:S.program),
      S.get_interface p1 = I.get_interface (compile p1).

  (* exact cc preserves also UB *)
  Axiom compiler_correctness :
    forall beh (p:S.program) (psi:interface),
      behaves (I.psem psi (SI.compile p)) beh ->
      behaves (S.psem psi p) beh.

  (* TODO This is too syntactic, it should be stated in terms of equivalent behaviors *)
  (* Only needed for RC variant *)
  Axiom separate_compilation:
    forall (P Q: S.program),
      map SI.compile (S.link Q P) = I.link (SI.compile Q) (SI.compile P).

  (* RC between S and I *)
  Definition RC:
    forall (c:I.program) (P:S.program) (beh:program_behavior),
      icomplete2 (I.get_interface c) (S.get_interface P) ->
      S.fully_defined (I.get_interface c) P ->
      behaves (I.osem (I.link c (SI.compile P))) beh
      ->
      exists C,
        behaves (S.osem (S.link C P)) beh /\ S.complete2 C P.
  Proof.
    intros c P b Hcomplete SFD H.
    apply I.decomposition in H.
    destruct (I.link_prepost c (SI.compile P)) as [p [H1 H2]].
    unfold I.complete2.
    rewrite <- SI.compiler_interfaces.
    auto.
    apply (SI.compiler_correctness b P (I.get_interface c)) in H.
    apply S.definability in H.
    destruct H as [C [Hb Hif]].
    exists C.
    split.
    auto.
    rewrite <- Hif in Hcomplete.
    auto.
    auto.
  Qed.

  (* This is proved using RC. *)
  Definition FD_preservation:
    forall (psi:interface) (p:S.program),
      S.fully_defined psi p ->
      I.fully_defined psi (SI.compile p).
  Proof.
    intros psi p SFD.
    intros b c Hpsi Hcomplete H1.
    unfold I.complete2 in Hcomplete.
    rewrite <- SI.compiler_interfaces in Hcomplete.
    destruct (SI.RC c p b Hcomplete) as [C [H2 H3]].
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
End SI.



(* Micro-policies target language *)
Module MP <: Lang.
  Axiom program : Type.
  Axiom get_interface: program -> interface.
  Definition complete (p:program) := icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := icomplete2 (get_interface p1) (get_interface p2).
  Axiom sem: program -> option semantics.
  Axiom psem: interface -> program -> option semantics.
  Definition osem (op: option program) := propagate sem op.
  Definition opsem i (op: option program) := propagate (psem i) op.
End MP.

(* Software Fault Isolation target language *)
Module SFI <: Lang.
  Axiom program : Type.
  Axiom get_interface: program -> interface.
  Definition complete (p:program) := icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := icomplete2 (get_interface p1) (get_interface p2).
  Axiom sem: program -> option semantics.
  Axiom psem: interface -> program -> option semantics.
  Definition osem (op: option program) := propagate sem op.
  Definition opsem i (op: option program) := propagate (psem i) op.
End SFI.


(* Interface expected by a compiler from Intermediate to Target
   Both backend MP and SFI need to implement this interface *)
Module Type IT.
  Declare Module T : Lang.
  
  (* TODO IT.compile must be a refinement compiler *)
  Axiom compile : I.program -> T.program.
  
  (* takes a complete program and produces a partial one
   This is an important ingredient for the simulation relation.
   For MP the relation corresponds with this function actually.
   For SFI the relation contains additional elements.
   *)
  Axiom partialize: interface -> T.program -> option T.program.
  Axiom partialize_post:
    forall (p:T.program) psi,
    exists pp, 
      (T.get_interface p) = (T.get_interface pp)++psi ->
      partialize psi p = Some pp.
  Definition opartialize psi (op: option T.program) := propagate (partialize psi) op.

  (* 
     The following properties are special because they depend on
     compiling the complete intermediate program.
   *)
  Axiom special_decomposition :
    forall beh (c p:I.program),
      I.fully_defined (I.get_interface c) p ->
      let ip := map compile (I.link c p) in
      behaves (T.osem ip) beh
      ->
      behaves (T.opsem (I.get_interface c) (opartialize (I.get_interface c) ip)) beh.

  Axiom special_compiler_correctness:
    forall beh (c p:I.program),
      I.fully_defined (I.get_interface c) p ->
      let ip := I.link c p in
      let tp := opartialize (I.get_interface c) (map compile ip) in
      behaves (T.opsem (I.get_interface c) tp) beh ->
      behaves (I.opsem (I.get_interface c) (Some p))  beh.
End IT.

(* Micro-policies compiler *)
Module MPC <: IT.
  Module T := MP.
  
  Axiom compile : I.program -> T.program.
  Axiom compile_complete :
    forall p1 p2,
      I.complete p1 -> compile p1 = p2 -> T.complete p2.
  
  Axiom compiler_interfaces:
    forall (p1:I.program),
      I.get_interface p1 = T.get_interface (compile p1).

  Axiom partialize: interface -> T.program -> option T.program.
  Axiom partialize_post:
    forall (p:T.program) psi,
    exists pp,
      (T.get_interface p) = (T.get_interface pp)++psi ->
      partialize psi p = Some pp.
  Definition opartialize psi (op: option T.program) := propagate (partialize psi) op.

  (* TODO prove assuming simulation *)
  Axiom decomposition:
    forall beh (p:T.program) psi,
      behaves (T.osem (Some p)) beh
      ->
      behaves (T.opsem psi (opartialize psi (Some p))) beh.
  
  (* we can prove special decomposition using the more general
     decomposition *)
  Definition special_decomposition :
    forall beh (c p:I.program),
      I.fully_defined (I.get_interface c) p ->
      let ip := map compile (I.link c p) in
      behaves (T.osem ip) beh
      ->
      behaves (T.opsem (I.get_interface c) (opartialize (I.get_interface c) ip)) beh.
  Proof.
    intros b c p IFD ip H.
    destruct ip.
    apply decomposition.
    assumption.
    simpl in H.
    auto.
  Qed.

  Axiom special_compiler_correctness:
    forall beh (c p:I.program),
      I.fully_defined (I.get_interface c) p ->
      let ip := I.link c p in
      let tp := opartialize (I.get_interface c) (map compile ip) in
      behaves (T.opsem (I.get_interface c) tp) beh ->
      behaves (I.opsem (I.get_interface c) (Some p))  beh.
End MPC.

(* Software Fault Isolation compiler *)
Module SFIC <: IT.
  Module T := SFI.
  
  Axiom compile : I.program -> T.program.
  Axiom compile_complete :
    forall p1 p2,
      I.complete p1 -> compile p1 = p2 -> T.complete p2.
  
  Axiom compiler_interfaces:
    forall (p1:I.program),
      I.get_interface p1 = T.get_interface (compile p1).

  Axiom partialize: interface -> T.program -> option T.program.
  Axiom partialize_post:
    forall (p:T.program) psi,
    exists pp,
      (T.get_interface p) = (T.get_interface pp)++psi ->
      partialize psi p = Some pp.
  Definition opartialize psi (op: option T.program) := propagate (partialize psi) op.

  (* there is no generic decomposition, we need to prove
      special_decomposition *)
  Axiom special_decomposition :
    forall beh (c p:I.program),
      I.fully_defined (I.get_interface c) p ->
      let ip := map compile (I.link c p) in
      behaves (T.osem ip) beh
      ->
      behaves (T.opsem (I.get_interface c) (opartialize (I.get_interface c) ip)) beh.

  Axiom special_compiler_correctness:
    forall beh (c p:I.program),
      I.fully_defined (I.get_interface c) p ->
      let ip := I.link c p in
      let tp := opartialize (I.get_interface c) (map compile ip) in
      behaves (T.opsem (I.get_interface c) tp) beh ->
      behaves (I.opsem (I.get_interface c) (Some p))  beh.
End SFIC.




(* The proof is modular wrt the backend *)
Module Main (IT : IT).
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
      behaves (IT.T.osem (map IT.compile (I.link c (SI.compile P)))) beh
      ->
      exists C, 
        behaves (S.osem (S.link C P)) beh /\ S.complete2 C P.

  Theorem proof_rc_static : robust_compilation_static_compromise.
  Proof.
    intros c P b Hcomplete SFD H.
    apply (IT.special_decomposition b c (SI.compile P)) in H.
    apply IT.special_compiler_correctness in H.
    destruct (S.definability b (I.get_interface c) P Hcomplete) as [C [H1 Hinterfaces]].
    apply (SI.compiler_correctness b P (I.get_interface c)) in H.
    assumption.
    rewrite <- Hinterfaces in Hcomplete.
    exists C.
    auto.
    apply SI.FD_preservation.
    assumption.
    apply SI.FD_preservation.
    assumption.
  Qed.


  (* This definition is weaker than the above but has the advantage of
   not mentioning the intermediate language *)
  Definition robust_compilation_static_compromise_corollary :=
    forall (Q P:S.program) (beh:program_behavior),
      S.complete2 Q P ->
      S.fully_defined (S.get_interface Q) P ->
      let compile := compose IT.compile SI.compile in
      behaves (IT.T.osem (map compile (S.link Q P))) beh ->
      exists C, behaves (S.osem (S.link C P)) beh /\ S.complete2 C P.

  Corollary robust_compilation_corrolary :
    robust_compilation_static_compromise ->
    robust_compilation_static_compromise_corollary.
  Proof.
    intros RC Q P b Hcompl H1 H2 H3.
    specialize (RC (SI.compile Q) P b).
    rewrite <- SI.compiler_interfaces in RC.
    unfold H2 in H3.
    rewrite <- SI.separate_compilation in RC.
    rewrite <- map_compose in H3.  
    apply (RC Hcompl H1 H3).
  Qed.

End Main.

Require Import Events.
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
(* check if a interface is contained in another *)
Definition contained {A} (i1 i2: list A) := exists i3, i1++i3=i2.



(* 
   The languages.
 *)

(* CH: In the end, moving valid into the program type (using a sigma
       type) might still be an option if it simplifies things and if
       no code that uses a program depends on the validity proof *)

(* Signature of basic things expected in a language *)
Module Type Lang.
  (* Type of programs, complete or partial *)
  Parameter program : Type.
  (* validity of program wrt to its interface, it's a relation between
     well-formed programs and their contained interfaces; it is
     a (not necessarily computable) partial function *)
  Parameter valid : program -> Prop.
  (* returns the interface of a program *)
  Parameter get_interface: program -> interface.

  (* The following 2 definitions are really always the same *)
  (* checks if a program has a complete interface *)
  Definition complete (p:program) :=
    valid p /\ icomplete (get_interface p).
  (* checks if two programs are valid and their interfaces are *)
  Definition complete2 (p1 p2:program) :=
    valid p1 /\ valid p2 /\
    icomplete2 (get_interface p1) (get_interface p2).

  (* CompCert defines the semantics of a program as an object providing the following:  
   state: Type.
   genvtype: Type.
   step : genvtype -> state -> trace -> state -> Prop.
   initial_state : program -> state -> Prop.
   final_state: state -> Prop.
   globalenv: program -> genvtype.

   any program has a semantics, if the program is ill-formed it
   still has a behavior. e.g. a program without any initial state
   satisfies program_goes_initially_wrong
   *)
  
  (* produces a complete semantics from a complete program *)
  Parameter sem: program -> semantics.
  
  (* produces a partial semantics from a complete program and an
     interface that is contained in it. The components of this interface
     will be ignored. *)
  (* TODO we should check that program is complete and interface is contained *)
  Parameter psem: interface -> program -> semantics.

End Lang.

(* Every language is a subtype of Lang and implements its signature *)
(* Note: most things are just axioms *)

(* Intermediate *)
Module I <: Lang.
  Axiom program : Type.
  Axiom valid: program -> Prop.
  Axiom get_interface: program -> interface.
  Definition complete (p:program) :=
    valid p /\ icomplete (get_interface p).
  Definition complete2 (p1 p2:program) :=
    valid p1 /\ valid p2 /\
    icomplete2 (get_interface p1) (get_interface p2).
    
  Axiom sem: program -> semantics.
  Axiom psem: interface -> program -> semantics.

  (* linking of two partial programs, this is restricted to the
     complete case, we could generalize by asking that p1 and p2 are
     compatible *)
  Axiom link: program -> program -> program.
  Axiom link_spec:
    forall (p1 p2 p:program),
      complete2 p1 p2 ->
      (get_interface p1) ++ (get_interface p2) = (get_interface p) /\
      complete (link p1 p2).

  (* TODO has p to be FD? *)
  Axiom decomposition:
    forall beh (c p:program),
      complete2 c p ->
      program_behaves (sem (link c p)) beh ->
      program_behaves (psem (get_interface c) p) beh.

  (* CH: TODO: I find the `valid` and `icomplete2` **preconditions** disturbing;
               this makes invalid or incomplete programs fully_defined *)
  Definition fully_defined (psi:interface) (p:program) :=
    valid p ->
    icomplete2 psi (get_interface p) ->
    forall (beh:program_behavior) (c:program),
      valid c ->
      get_interface c = psi ->
      program_behaves (sem (link c p)) beh ->
      (turn beh (get_interface p) ->
       not_wrong beh).
End I.

(* Source *)
Module S <: Lang.
  Axiom program : Type.
  Axiom valid: program -> Prop.
  Axiom get_interface: program -> interface.
  Definition complete (p:program) :=
    valid p /\ icomplete (get_interface p).
  Definition complete2 (p1 p2:program) :=
    valid p1 /\ valid p2 /\
    icomplete2 (get_interface p1) (get_interface p2).
  Axiom sem: program -> semantics.
  Axiom psem: interface -> program -> semantics.
  
  Axiom link: program -> program -> program.

  Definition fully_defined (psi:interface) (p:program) :=
    valid p ->
    icomplete2 psi (get_interface p) ->
    forall (beh:program_behavior) (c:program),
      valid c ->
      get_interface c = psi ->
      program_behaves (sem (link c p)) beh ->
      (turn beh (get_interface p) ->
       not_wrong beh).

  Axiom definability:
    forall (beh:program_behavior) (psi:interface) (p:program),
      valid p ->
      icomplete2 psi (get_interface p) ->
      fully_defined psi p ->
      program_behaves (psem psi p) beh ->
      exists (c:program),
        valid c /\
        get_interface c = psi /\
        fully_defined (get_interface p) c /\
        program_behaves (sem (link c p)) beh.

  (* TODO also works for UB *)
  Axiom decomposition:
    forall beh (c p:program),
      complete2 c p ->
      program_behaves (sem (link c p)) beh ->
      program_behaves (psem (get_interface c) p) beh.
End S.

(* Source to Intermediate *)
Module SI.
  (* TODO
     compcert defined the compiler as:
     - a function transf_c_program (p: Csyntax.program) : res Asm.program
     - a relation match_prog: Csyntax.program -> Asm.program -> Prop
     and proves their equivalence in transf_c_program_match.
 *)
  (* compiles partial programs *)
  Axiom compile : S.program -> I.program.
  Axiom compile_spec:
    forall (p:S.program),
      S.valid p ->
      I.valid (compile p) /\ S.get_interface p = I.get_interface (compile p).

  (* TODO it also preserves UB; CH: needed for preserving FD *)
  Axiom compiler_correctness :
    forall beh (P:S.program) (psi:interface),
      S.valid P ->
      icomplete2 psi (S.get_interface P) ->
      S.fully_defined psi P ->
      program_behaves (I.psem psi (SI.compile P)) beh <->
      program_behaves (S.psem psi P) beh.

  (* RC between S and I *)
  Definition RC:
    forall (c:I.program) (P:S.program) (beh:program_behavior),
      S.valid P ->
      I.valid c ->
      icomplete2 (I.get_interface c) (S.get_interface P) ->
      S.fully_defined (I.get_interface c) P ->
      program_behaves (I.sem (I.link c (SI.compile P))) beh ->
      exists C,
        program_behaves (S.sem (S.link C P)) beh /\ S.complete2 C P.
  Proof.
    intros c P b HvalP Hvalc Hcompl PFD H.
    assert (PFD2 := PFD).
    specialize (PFD2 HvalP Hcompl).
    destruct (compile_spec P HvalP) as [HvalPcom Hcompint].
    apply I.decomposition in H.
    apply (compiler_correctness b P (I.get_interface c) HvalP Hcompl PFD) in H.
    destruct (S.definability b (I.get_interface c) P HvalP Hcompl PFD H) as [C [HvalC [Hif [CFD H2]]]].
    exists C.
    split; auto.
    unfold S.complete2.
    repeat split; auto.
    rewrite <- Hif in Hcompl.
    repeat split; auto.
    unfold I.complete2.
    repeat split;auto.
    rewrite <- Hcompint.
    auto.
  Qed.

  (* This is proved using RC. *)
  Definition FD_preservation:
    forall (psi:interface) (P:S.program),
      S.valid P ->
      icomplete2 psi (S.get_interface P) ->
      S.fully_defined psi P ->
      I.fully_defined psi (SI.compile P).
  Proof.
    intros psi P HvalP Hicompl PFD.
    assert (PFD2 := PFD).
    unfold I.fully_defined.
    intros HvalPcom Hifcomp b c Hvalc Hifc H.
    apply I.decomposition in H.
    apply compiler_correctness in H.
    apply S.definability in H as [C [HvalC [Cif [CFD H2]]]].
    assert (HvalP2 := HvalP).
    apply (compile_spec P) in HvalP2 as [_ Hifcom].
    rewrite <- Hifcom.
    rewrite Hifc in Cif.
    specialize (PFD2 HvalP Hicompl b C HvalC Cif H2).
    auto.
    auto.
    rewrite Hifc. auto.
    rewrite Hifc. auto.
    auto.
    rewrite Hifc. auto.
    rewrite Hifc. auto.
    unfold I.complete2.
    split; auto.
    split; auto.
    rewrite <- Hifc in Hifcomp. auto.
Qed.
End SI.



(* Micro-policies target language *)
Module MP <: Lang.
  Axiom program : Type.
  Axiom valid: program -> Prop.
  Axiom get_interface: program -> interface.
  Definition complete (p:program) := valid p /\ icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := valid p1 /\ valid p2 /\ icomplete2 (get_interface p1) (get_interface p2).
  Axiom sem: program -> semantics.
  Axiom psem: interface -> program -> semantics.
End MP.

(* Software Fault Isolation target language *)
Module SFI <: Lang.
  Axiom program : Type.
  Axiom valid: program -> Prop.
  Axiom get_interface: program -> interface.
  Definition complete (p:program) := valid p /\ icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := valid p1 /\ valid p2 /\ icomplete2 (get_interface p1) (get_interface p2).
  Axiom sem: program -> semantics.
  Axiom psem: interface -> program -> semantics.
End SFI.


(* Interface expected for a compiler from Intermediate to Target
   Both backend MP and SFI need to implement this interface *)
Module Type IT.
  Declare Module T : Lang.
  
  (* TODO
     compcert defines the compiler as:
     - a function transf_c_program (p: Csyntax.program) : res Asm.program
     - a relation match_prog: Csyntax.program -> Asm.program -> Prop
     and proves their equivalence in transf_c_program_match.
   *)
  (* TODO is IT.compile a refinement compiler? CH: No undef refinement *)
  (* Note that this compiler only works on complete programs as
     opposed to the SI.compile that works on partial programs *)
  Parameter compile : I.program -> T.program.
  Parameter compile_spec:
    forall (p:I.program),
      I.complete p -> T.valid (compile p) /\
                   I.get_interface p = T.get_interface (compile p).
  
  (* takes a complete program and an interface. The components of the
     interface will be erased from memory.
     This is an important ingredient for the simulation relation.
     For MP the relation corresponds with this function actually.
     For SFI the relation contains additional elements.
   *)
  Parameter partialize: interface -> T.program -> T.program.
  Parameter partialize_spec:
    forall psi (p:T.program),
      T.valid p ->
      contained psi (T.get_interface p) ->
      (T.get_interface p) = (T.get_interface (partialize psi p))++psi.

  (* 
     The following properties are special because they depend on
     compiling the complete intermediate program.
   *)
  Parameter special_decomposition :
    forall beh (c p:I.program),
      I.complete2 c p ->
      I.fully_defined (I.get_interface c) p ->
      let ip := compile (I.link c p) in
      program_behaves (T.sem ip) beh ->
      program_behaves (T.psem (I.get_interface c) ip) beh.

  Parameter special_compiler_correctness:
    forall beh (c p:I.program),
      I.complete2 c p ->
      I.fully_defined (I.get_interface c) p ->
      let ip := I.link c p in
      program_behaves (T.psem (I.get_interface c) (compile ip)) beh ->
      program_behaves (I.psem (I.get_interface c) p)  beh.
End IT.

(* Micro-policies compiler *)
Module MPC <: IT.
  Module T := MP.
  
  Axiom compile : I.program -> T.program.
  Axiom compile_spec:
    forall (p:I.program),
      I.complete p -> T.valid (compile p) /\
                   I.get_interface p = T.get_interface (compile p).

  Axiom partialize: interface -> T.program -> T.program.
  Axiom partialize_spec:
    forall psi (p:T.program),
      T.valid p ->
      contained psi (T.get_interface p) ->
      (T.get_interface p) = (T.get_interface (partialize psi p))++psi.

  (* Axiom forward_simulation_behavior: *)
  (*   forall p psi, *)
  (*     T.complete p -> *)
  (*     contained psi (T.get_interface p) -> *)
  (*     exists (cs ps:semantics) f, f=forward_simulation cs ps. *)
    
  (*   Theorem forward_simulation_behavior: *)
  (*   forall p psi cs ps, *)
  (*     T.sem p = Some cs -> *)
  (*     T.opsem psi (partialize psi p) = Some ps -> *)
  (*     forward_simulation cs ps -> *)
  (*     forall beh1, program_behaves cs beh1 -> *)
  (*                  program_behaves ps beh1. *)
  (* Proof. *)
  (*   intros p psi cs ps Hsem Hpsem Hfs b H1. *)
    
  (* TODO prove assuming simulation *)
  Axiom decomposition:
    forall beh psi (p:T.program),
      T.valid p ->
      contained psi (T.get_interface p) ->
      program_behaves (T.sem p) beh ->
      program_behaves (T.psem psi p) beh.
  
  (* we can prove special decomposition using the more general
     decomposition *)
  Definition special_decomposition :
    forall beh (c p:I.program),
      I.complete2 c p ->
      I.fully_defined (I.get_interface c) p ->
      let ip := compile (I.link c p) in
      program_behaves (T.sem ip) beh ->
      program_behaves (T.psem (I.get_interface c) ip) beh.
  Proof.
    intros b c p Hcomp pFD tp H.
    destruct (I.link_spec c p (I.link c p) Hcomp) as [Hif [Hvalip Hcompip]].
    destruct (compile_spec (I.link c p)) as [HvalPcom Hcompint].
    unfold I.complete.
    split; auto.
    apply decomposition.
    assumption.
    unfold contained.
    exists (I.get_interface p).
    rewrite Hcompint in Hif.
    assumption.
    assumption.
  Qed.

  Axiom special_compiler_correctness:
    forall beh (c p:I.program),
      I.complete2 c p ->
      I.fully_defined (I.get_interface c) p ->
      let ip := I.link c p in
      program_behaves (T.psem (I.get_interface c) (compile ip)) beh ->
      program_behaves (I.psem (I.get_interface c) p)  beh.
End MPC.

(* Software Fault Isolation compiler *)
Module SFIC <: IT.
  Module T := SFI.
  
  Axiom compile : I.program -> T.program.
  Axiom compile_spec:
    forall (p:I.program),
      I.complete p -> T.valid (compile p) /\
                   I.get_interface p = T.get_interface (compile p).

  Axiom partialize: interface -> T.program -> T.program.
  Axiom partialize_spec:
    forall psi (p:T.program),
      T.valid p ->
      contained psi (T.get_interface p) ->
      (T.get_interface p) = (T.get_interface (partialize psi p))++psi.

  (* there is no generic decomposition, we need to prove
      special_decomposition *)
  Parameter special_decomposition :
    forall beh (c p:I.program),
      I.complete2 c p ->
      I.fully_defined (I.get_interface c) p ->
      let ip := compile (I.link c p) in
      program_behaves (T.sem ip) beh ->
      program_behaves (T.psem (I.get_interface c) ip) beh.

  Axiom special_compiler_correctness:
    forall beh (c p:I.program),
      I.complete2 c p ->
      I.fully_defined (I.get_interface c) p ->
      let ip := I.link c p in
      program_behaves (T.psem (I.get_interface c) (compile ip)) beh ->
      program_behaves (I.psem (I.get_interface c) p)  beh.
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
      I.valid c ->
      S.valid P ->
      icomplete2 (I.get_interface c) (S.get_interface P) ->
      S.fully_defined (I.get_interface c) P ->
      program_behaves (IT.T.sem (IT.compile (I.link c (SI.compile P)))) beh
      ->
      exists C,
        S.valid C ->
        S.get_interface C = I.get_interface c /\
        S.fully_defined (S.get_interface P) C /\ 
        program_behaves (S.sem (S.link C P)) beh.

  Theorem proof_rc_static : robust_compilation_static_compromise.
  Proof.
    intros c P b Hvalc HvalP Hicompl PFD H.
    assert (PFD2 := PFD).
    destruct (SI.compile_spec P HvalP) as [HvalPcom Hifcom].
    apply (IT.special_decomposition b c (SI.compile P)) in H.
    apply IT.special_compiler_correctness in H.
    destruct (S.definability b (I.get_interface c) P HvalP Hicompl PFD) as [C [HvalC [Cif [CFDs H2]]]].
    apply (SI.compiler_correctness b P (I.get_interface c)) in H.
    assumption.
    assumption.
    auto.
    auto.
    exists C.
    split.
    auto.
    split; auto.
    unfold I.complete2.
    split; auto.
    split; auto.
    rewrite <- Hifcom.
    auto.
    apply SI.FD_preservation.
    assumption.
    assumption.
    assumption.
    unfold I.complete2.
    split; auto.
    split; auto.
    rewrite <- Hifcom.
    auto.
    apply SI.FD_preservation.
    assumption.
    assumption.
    assumption.
  Qed.


  (* This property is strictly weaker than the above, but has the
     advantage of not mentioning the intermediate language *)
  Definition robust_compilation_static_compromise_weaker :=
    forall (Q P:S.program) (beh:program_behavior),
      S.complete2 Q P ->
      S.fully_defined (S.get_interface Q) P ->
      program_behaves (IT.T.sem (IT.compile (I.link (SI.compile Q) (SI.compile P)))) beh ->
      exists C,
        S.valid C ->
        S.get_interface C = S.get_interface Q /\
        S.fully_defined (S.get_interface P) C /\ 
        program_behaves (S.sem (S.link C P)) beh.

  Corollary robust_compilation_corrolary :
    robust_compilation_static_compromise ->
    robust_compilation_static_compromise_weaker.
  Proof.
    intros RC Q P b Hcompl SFD H2.
    specialize (RC (SI.compile Q) P b).
    assert (SFD2 := SFD).
    assert (Hcompl2 := Hcompl).
    destruct Hcompl2 as [HvalQ [HvalP Hicompl]].
    destruct (SI.compile_spec Q).
    auto.
    rewrite <- H0 in RC.
    apply (RC H HvalP Hicompl SFD H2).
  Qed.

End Main.

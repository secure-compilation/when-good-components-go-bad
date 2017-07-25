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
Definition contained {A} (i1 i2: list A) := exists i3, i1++i3=i2.
(* TODO check this *)
Axiom unique_interfaces :
  forall (i1 i2 i3:interface),
    icomplete2 i1 i3 -> icomplete2 i2 i3 -> i1=i2.


(* 
   The languages.
 *)

(* Signature of basic things expected in a language *)
Module Type Lang.
  (* Type of programs, complete or partial *)
  Parameter program : Type.
  (* relation between well-formed programs and their corresponding
     interfaces; has_interface is a (not necessarily computable) 
     partial function *)
  Parameter valid : program -> Prop.
  Parameter get_interface: program -> interface.
  (* Parameter get_interface_spec: *)
  (*   forall p, valid p -> exists i, get_interface p = Some i. *)
  
  (* checks if a program has a complete interface *)
  Parameter complete: program -> Prop.
  (* Parameter complete_spec: *)
  (*   forall p, valid p -> exists i, get_interface p = Some i /\ complete p = icomplete i. *)
  
  (* checks if two programs linked together form a complete program *)
  Parameter complete2: program -> program -> Prop.

  (* Parameter state: Type. *)
  (* Parameter genvtype: Type. *)
  (* Parameter step : genvtype -> state -> trace -> state -> Prop. *)
  (* Parameter initial_state : program -> state -> Prop. *)
  (* Parameter final_state: state -> Prop. *)
  (* Parameter globalenv: program -> genvtype. *)

  (* Definition sem (p: program) : semantics := *)
  (*   let ge := globalenv p in *)
  (*   Semantics_gen step (initial_state p) final_state ge. *)
  
  (* complete semantics: takes a complete program *)
  Parameter sem: program -> semantics.
  (* any program has a semantics, if the program is ill-formed it still has a behavior.
     e.g. a program without any initial state satisfies program_goes_initially_wrong *)
  
  (* partial semantics: takes a program and a matching interface.
     The interface of the program together with the matching interface
     is complete. *)
  Parameter psem: interface -> program -> semantics.

  (* Axiom idefinability: forall (i:interface), exists (p:program), get_interface p = i. *)
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
    valid p1 /\
    valid p2 /\
    icomplete2 (get_interface p1) (get_interface p2).
    
  Axiom sem: program -> semantics.
  Axiom psem: interface -> program -> semantics.

  (* linking of two partial programs, this is restricted to the
     complete case, we could generalize by asking that p1 and p2 are
     compatible *)
  Axiom link: program -> program -> program.
  Axiom link_spec:
    forall (p1 p2:program),
      valid p1 /\ valid p2 /\ complete2 p1 p2 ->
      exists (p:program),
        (get_interface p1) ++ (get_interface p2) = (get_interface p) /\
        valid p /\ complete p.

  (* only for the safe case *)
  (* TODO has p to be FD? *)
  Axiom decomposition:
    forall beh (c p:I.program),
      complete2 c p ->
      program_behaves (sem (link c p)) beh ->
      not_wrong beh ->
      program_behaves (psem (get_interface c) p) beh.
  
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
    valid p1 /\
    valid p2 /\
    icomplete2 (get_interface p1) (get_interface p2).
  Axiom sem: program -> semantics.
  Axiom psem: interface -> program -> semantics.

  Axiom link: program -> program -> program.

  Definition fully_defined (psi:interface) (p:program) :=
    valid p /\
    icomplete2 psi (get_interface p) /\
    forall (beh:program_behavior) (c:program),
      valid c ->
      get_interface c = psi ->
      program_behaves (sem (link c p)) beh ->
      (turn beh (get_interface p) ->
       not_wrong beh).

  (* TODO can beh be UB? *)
  (* TODO if P is FD then we can argue that beh is not wrong *)
  Axiom definability:
    forall (beh:program_behavior) (psi:interface) (p:program),
      valid p ->
      icomplete2 psi (get_interface p) ->
      program_behaves (psem psi p) beh ->
      (* not_wrong beh -> *)
      exists (c:program),
        program_behaves (sem (link c p)) beh /\ valid c /\ get_interface c = psi.
End S.

(* Source to Intermediate *)
Module SI.
  (* TODO
     compcert defined the compiler as:
     - a function transf_c_program (p: Csyntax.program) : res Asm.program
     - a relation match_prog: Csyntax.program -> Asm.program -> Prop
     and proves their equivalence in transf_c_program_match.
 *)
  Axiom compile : S.program -> I.program.
  Axiom compile_spec:
    forall (p:S.program),
      S.valid p ->
      I.valid (compile p) /\ S.get_interface p = I.get_interface (compile p).

  (* TODO does it preserve also UB? *)
  Axiom compiler_correctness :
    forall beh (p:S.program) (psi:interface),
      S.valid p ->
      icomplete2 psi (S.get_interface p) ->
      program_behaves (I.psem psi (SI.compile p)) beh ->
      program_behaves (S.psem psi p) beh.

  (* TODO This is too syntactic, it should be stated in terms of 
     equivalent behaviors *)
  (* Only needed for RC variant *)
  Axiom separate_compilation:
    forall (P Q: S.program),
      S.complete2 Q P ->
      SI.compile (S.link Q P) = I.link (SI.compile Q) (SI.compile P).

  (* RC between S and I *)
  Definition RC:
    forall (c:I.program) (P:S.program) (beh:program_behavior),
      S.fully_defined (I.get_interface c) P ->
      I.valid c ->
      program_behaves (I.sem (I.link c (SI.compile P))) beh ->
      not_wrong beh ->
      exists C,
        program_behaves (S.sem (S.link C P)) beh /\ S.complete2 C P.
  Proof.
    intros c P b [HvalP [Hcomplete H1]] Hvalc H Hsafe.
    destruct (compile_spec P HvalP) as [H2 Hcompint].
    apply I.decomposition in H.
    apply (SI.compiler_correctness b P (I.get_interface c)) in H.
    destruct (S.definability b (I.get_interface c) P HvalP Hcomplete H) as [C [Hb [HvalC Hif]]].
    auto.
    exists C.
    split; auto.
    unfold S.complete2.
    rewrite <- Hif in Hcomplete.
    repeat split; auto.
    all: auto.
    repeat split;auto.
    rewrite <- Hcompint.
    auto.
  Qed.

  (* Require Import Coq.Logic.Classical. *)

  (* This is proved using RC. *)
  Definition FD_preservation:
    forall (psi:interface) (P:S.program),
      S.fully_defined psi P ->
      I.fully_defined psi (SI.compile P).
  Proof.
    intros psi P SFD.
    (* assert (SFD2 := SFD). *)
    unfold I.fully_defined.
    intros p Hcomplete b c Hvalc Hif Hbeh.
    rewrite <- Hif in SFD.
    destruct (SI.RC c P b SFD Hvalc) as [C [H3 H4]].
    (* destruct (classic (turn b (S.get_interface p))). *)
    (* destruct (classic (not_wrong b )). *)
    (* destruct SFD as [Hvalp [H88 HFD]]. *)
    (* destruct (compile_spec p Hvalp) as [Hvalcomp Hint2]. *)
    (* rewrite <- Hint2. *)
    (* destruct SFD as [Hvalp [H88 HFD]]. *)
    (* destruct (compile_spec p Hvalp) as [Hvalcomp Hint]. *)
    (* apply not_all_ex_not in H0 as [b1 NW]. *)
    (* destruct (compile_spec p Hvalp) as [Hvalcomp Hint]. *)
    (* destruct (unique_interfaces (I.get_interface c) (S.get_interface C) (S.get_interface p)). *)
  Admitted.
End SI.



(* Micro-policies target language *)
Module MP <: Lang.
  Axiom program : Type.
  Axiom valid: program -> Prop.
  Axiom get_interface: program -> interface.
  Definition complete (p:program) := icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := icomplete2 (get_interface p1) (get_interface p2).
  Axiom sem: program -> semantics.
  Axiom psem: interface -> program -> semantics.
End MP.

(* Software Fault Isolation target language *)
Module SFI <: Lang.
  Axiom program : Type.
  Axiom valid: program -> Prop.
  Axiom get_interface: program -> interface.
  Definition complete (p:program) := icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := icomplete2 (get_interface p1) (get_interface p2).
  Axiom sem: program -> semantics.
  Axiom psem: interface -> program -> semantics.
End SFI.


(* Interface expected by a compiler from Intermediate to Target
   Both backend MP and SFI need to implement this interface *)
Module Type IT.
  Declare Module T : Lang.
  
  (* TODO
     compcert defined the compiler as:
     - a function transf_c_program (p: Csyntax.program) : res Asm.program
     - a relation match_prog: Csyntax.program -> Asm.program -> Prop
     and proves their equivalence in transf_c_program_match.
 *)
  (* TODO IT.compile must be a refinement compiler *)
  Parameter compile : I.program -> T.program.
  Axiom compile_spec:
    forall (p:I.program),
      I.valid p -> T.valid (compile p) /\
                   I.get_interface p = T.get_interface (compile p).
  
  (* takes a complete program and produces a partial one
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
      I.fully_defined (I.get_interface c) p ->
      let ip := compile (I.link c p) in
      program_behaves (T.sem ip) beh
      ->
      program_behaves (T.psem (I.get_interface c) (partialize (I.get_interface c) ip)) beh.

  Parameter special_compiler_correctness:
    forall beh (c p:I.program),
      I.fully_defined (I.get_interface c) p ->
      let ip := I.link c p in
      let tp := partialize (I.get_interface c) (compile ip) in
      program_behaves (T.psem (I.get_interface c) tp) beh ->
      program_behaves (I.psem (I.get_interface c) p)  beh.
End IT.

(* Micro-policies compiler *)
Module MPC <: IT.
  Module T := MP.
  
  Axiom compile : I.program -> T.program.
  Axiom compile_spec:
    forall (p:I.program),
      I.valid p -> T.valid (compile p) /\
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
  Axiom partialize_decomposition:
    forall beh (p:T.program) psi,
      program_behaves (T.sem p) beh
      ->
      program_behaves (T.psem psi (partialize psi p)) beh.
  
  (* we can prove special decomposition using the more general
     decomposition *)
  Definition special_decomposition :
    forall beh (c p:I.program),
      I.fully_defined (I.get_interface c) p ->
      let ip := compile (I.link c p) in
      program_behaves (T.sem ip) beh
      ->
      program_behaves (T.psem (I.get_interface c) (partialize (I.get_interface c) ip)) beh.
  Proof.
    intros b c p IFD ip H.
    apply partialize_decomposition.
    assumption.
  Qed.

  Axiom special_compiler_correctness:
    forall beh (c p:I.program),
      I.fully_defined (I.get_interface c) p ->
      let ip := I.link c p in
      let tp := partialize (I.get_interface c) (compile ip) in
      program_behaves (T.psem (I.get_interface c) tp) beh ->
      program_behaves (I.psem (I.get_interface c) p)  beh.
End MPC.

(* Software Fault Isolation compiler *)
Module SFIC <: IT.
  Module T := SFI.
  
  Axiom compile : I.program -> T.program.
  Axiom compile_spec:
    forall (p:I.program),
      I.valid p -> T.valid (compile p) /\
                   I.get_interface p = T.get_interface (compile p).

  Axiom partialize: interface -> T.program -> T.program.
  Axiom partialize_spec:
    forall psi (p:T.program),
      T.valid p ->
      contained psi (T.get_interface p) ->
      (T.get_interface p) = (T.get_interface (partialize psi p))++psi.

  (* there is no generic decomposition, we need to prove
      special_decomposition *)
  Axiom special_decomposition :
    forall beh (c p:I.program),
      I.fully_defined (I.get_interface c) p ->
      let ip := compile (I.link c p) in
      program_behaves (T.sem ip) beh
      ->
      program_behaves (T.psem (I.get_interface c) (partialize (I.get_interface c) ip)) beh.

  Axiom special_compiler_correctness:
    forall beh (c p:I.program),
      I.fully_defined (I.get_interface c) p ->
      let ip := I.link c p in
      let tp := partialize (I.get_interface c) (compile ip) in
      program_behaves (T.psem (I.get_interface c) tp) beh ->
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
      icomplete2 (I.get_interface c) (S.get_interface P) ->
      S.fully_defined (I.get_interface c) P ->
      program_behaves (IT.T.sem (IT.compile (I.link c (SI.compile P)))) beh
      ->
      exists C, S.fully_defined (S.get_interface P) C /\ S.complete2 C P /\
        program_behaves (S.sem (S.link C P)) beh.

  Theorem proof_rc_static : robust_compilation_static_compromise.
  Proof.
    intros c P b Hcomplete SFD H.
    apply (IT.special_decomposition b c (SI.compile P)) in H.
    apply IT.special_compiler_correctness in H.
    destruct SFD as [HvalP [_ HFD]].
    destruct (S.definability b (I.get_interface c) P HvalP Hcomplete) as [C [H1 [HvalC Hif]]].
    apply (SI.compiler_correctness b P (I.get_interface c)) in H.
    assumption.
    assumption.
    assumption.
    rewrite <- Hif in Hcomplete.
    exists C.
    split.
    auto.
    unfold S.complete2.
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
      program_behaves (IT.T.sem (compile (S.link Q P))) beh ->
      exists C, S.fully_defined (S.get_interface P) C /\ S.complete2 C P /\ program_behaves (S.sem (S.link C P)) beh.

  Corollary robust_compilation_corrolary :
    robust_compilation_static_compromise ->
    robust_compilation_static_compromise_corollary.
  Proof.
    intros RC Q P b Hcompl SFD H2 H3.
    specialize (RC (SI.compile Q) P b).
    assert (SFD2 := SFD).
    destruct SFD2 as [HvalP [_ HFD]].
    assert (Hcompl2 := Hcompl).
    destruct Hcompl2 as [HvalQ [_ Hicompl]].
    destruct (SI.compile_spec Q).
    auto.
    rewrite <- H0 in RC.
    rewrite <- SI.separate_compilation in RC.
    apply (RC Hicompl SFD H3).
    apply Hcompl.
  Qed.

End Main.

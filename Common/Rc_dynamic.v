Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Common.Definitions.

(* 
   Top-down proof of Robust Compilation Dynamic Compromise relying on 
   - target decomposition
   - compiler correctness 
   - source definability
 *)

(*
  Some Global definitions.
 *)

(* Component id *)
Definition interface := list Component.id.
(* check if an interface is complete *)
Axiom icomplete : interface -> Prop.
(* check if the union of two interfaces is complete *)
Definition icomplete2 (i1 i2:interface) := icomplete (i1++i2).
(* check if a interface is contained in another *)
Definition contained {A} (i1 i2: list A) := exists i3, i1++i3=i2.

(* A partition is less than an inteface and will simplify proofs. *)
Definition partition := list Component.id.
(* check if the last event of a behavior belongs to an agent,
   represented by the interface of its components *)
Definition turn_trace (t:trace) (par:partition) : Prop :=
  forall e, exists t', t = e::t' /\
             (match e with
              | ECall Cid Pid n Cid' => In Cid' par
              | ERet Cid n Cid' => In Cid' par
              end).
(* turn is defined only for finite traces. *)
Definition turn (b:program_behavior) (i:partition) : Prop :=
  exists t, turn_trace t i /\
            ((exists n, b = Terminates t n) \/
            (b = Diverges t) \/
            (b = Goes_wrong t)).
Definition behavior_improves_p (behs beht:program_behavior) (par:partition) :=
  (behs = beht \/ (exists t, behs = Goes_wrong t /\
                             behavior_prefix t beht /\
                             turn behs par)).

Lemma behavior_improves_p_trans:
  forall beh1 beh2 beh3 p,
  behavior_improves_p beh1 beh2 p -> behavior_improves_p beh2 beh3 p ->
  behavior_improves_p beh1 beh3 p.
Proof. Admitted.

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

  (* In CompCert any program has a semantics, if the program is
   ill-formed it still has a behavior. e.g. a program without any
   initial state satisfies program_goes_initially_wrong *)
  
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

  Axiom decomposition:
    forall beh (c p:program),
      complete2 c p ->
      program_behaves (sem (link c p)) beh ->
      program_behaves (psem (get_interface c) p) beh.

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

  Axiom definability:
    forall (beh:program_behavior) (psi:interface) (p:program),
      valid p ->
      icomplete2 psi (get_interface p) ->
      program_behaves (psem psi p) beh ->
      exists (c:program),
        valid c /\
        get_interface c = psi /\
        program_behaves (sem (link c p)) beh.
End S.

(* Source to Intermediate *)
Module SI.
  (* compiles partial programs *)
  Axiom compile : S.program -> I.program.
  Axiom compile_spec:
    forall (p:S.program),
      S.valid p ->
      I.valid (compile p) /\ S.get_interface p = I.get_interface (compile p).

  Axiom Sreceptive:
    forall P, receptive (S.sem P).
  Axiom Ideterminate:
    forall p, determinate (I.sem p).

  (* In compcert there are two simulation: *)
  (*   - forward: is just a simulation, it is forward or backward depending on the order of the arguments *)
  (*   - backward: add the condition that the first argument must be a safe program *)

  Axiom complete_forward_simulation :
    forall P,
      S.complete P ->
      forward_simulation (S.sem P) (I.sem (compile P)).

  Definition complete_backward_simulation:
    forall P,
      S.complete P ->
      backward_simulation (S.sem P) (I.sem (compile P)).
  Proof.
    intros. apply forward_to_backward_simulation.
    apply complete_forward_simulation.
    auto. auto.
    apply Sreceptive. apply Ideterminate.
  Qed.

  (* TODO this shoudl be improves_p *)
  Theorem complete_compiler_correctness:
    forall P behi,
      S.complete P ->
      program_behaves (I.sem (compile P)) behi ->
      exists behs, program_behaves (S.sem P) behs /\ behavior_improves behs behi.
  Proof.
    intros. eapply backward_simulation_behavior_improves; eauto.
    apply complete_backward_simulation; auto.
  Qed.

  (* this should be provable from the complete backward simulation *)
  Axiom partial_backward_simulation:
    forall P psi,
      S.valid P ->
      icomplete2 psi (S.get_interface P) ->
      backward_simulation (S.psem psi P) (I.psem psi (compile P)).

  Axiom partial_backward_simulation_behavior_improves_p:
    forall psi p1 p2,
      backward_simulation (S.psem psi p1) (I.psem psi p2) ->
    forall behi, program_behaves (I.psem psi p2) behi ->
    exists behs, program_behaves (S.psem psi p1) behs /\ behavior_improves_p behs behi (S.get_interface p1).
    
  Theorem partial_compiler_correctness:
    forall P psi behi,
      S.valid P ->
      icomplete2 psi (S.get_interface P) ->
      program_behaves (I.psem psi (compile P)) behi ->
      exists behs, program_behaves (S.psem psi P) behs /\ behavior_improves_p behs behi (S.get_interface P).
  Proof.
    intros. eapply partial_backward_simulation_behavior_improves_p; eauto.
    apply partial_backward_simulation; auto.
  Qed.
End SI.



(* Micro-policies target language *)
Module MP <: Lang.
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
End MP.

(* Software Fault Isolation target language *)
Module SFI <: Lang.
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
End SFI.


(* Interface expected for a compiler from Intermediate to Target
   Both backend MP and SFI need to implement this interface *)
Module Type IT.
  Declare Module T : Lang.
  (* Note that 
     - this compiler only works on complete programs as
       opposed to SI.compile that works on partial programs 
     - undefined programs, such as a context linked with a FD program,
       will have a defined behavior once compiled.
       TODO do we provide any guarantee in that case?
   *)
  Parameter compile : I.program -> T.program.
  Parameter compile_spec:
    forall (p:I.program),
      I.complete p -> T.valid (compile p) /\
                   I.get_interface p = T.get_interface (compile p).
  
  (* 
     The following properties are special because they depend on
     compiling the complete intermediate program.
     Note:
     - the compiled program doesn't have any UB so we don't need to
       preserve it.
   *)
  Parameter special_decomposition :
    forall beh (c p:I.program),
      I.complete2 c p ->
      let ip := compile (I.link c p) in
      program_behaves (T.sem ip) beh ->
      program_behaves (T.psem (I.get_interface c) ip) beh.

  Parameter special_compiler_correctness:
    forall (beht:program_behavior) (c p:I.program),
      I.complete2 c p ->
      let ip := I.link c p in
      program_behaves (T.psem (I.get_interface c) (compile ip)) beht ->
      exists behi,
      program_behaves (I.psem (I.get_interface c) p) behi /\
      behavior_improves_p behi beht (I.get_interface p).

  (* At target level all behaviors are defined, if the program is
     ill-formed the behavior is termination *)
  Parameter sem_spec:
    forall p b, program_behaves (T.sem p) b -> not_wrong b.
End IT.

(* Micro-policies compiler *)
Module MPC <: IT.
  Module T := MP.
  
  Axiom compile : I.program -> T.program.
  Axiom compile_spec:
    forall (p:I.program),
      I.complete p -> T.valid (compile p) /\
                   I.get_interface p = T.get_interface (compile p).

  (* this would be used in the definition of T.psem and in match_states *)
  (* Axiom partialize: interface -> T.program -> T.program. *)
  (* Axiom partialize_spec: *)
  (*   forall psi (p:T.program), *)
  (*     T.valid p -> *)
  (*     contained psi (T.get_interface p) -> *)
  (*     (T.get_interface p) = (T.get_interface (partialize psi p))++psi. *)

  Axiom sem_spec:
    forall p b, program_behaves (T.sem p) b -> not_wrong b.

  Axiom psem_spec:
    forall psi p b, program_behaves (T.psem psi p) b -> not_wrong b.

  (* assuming we have a simulation *)
  Axiom decomposition_simulation:
    forall psi tp,
    forward_simulation (T.sem tp) (T.psem psi tp).
    
  Definition decomposition:
    forall beh psi (p:T.program),
      T.valid p ->
      contained psi (T.get_interface p) ->
      program_behaves (T.sem p) beh ->
      program_behaves (T.psem psi p) beh.
  Proof.
    intros b psi p Hvalp Hcont Hsem.
    eapply forward_simulation_same_safe_behavior.
    apply decomposition_simulation.
    assumption.
    apply (sem_spec p).
    assumption.
  Qed.
  
  (* we can prove special decomposition using the more general *)
  (*      decomposition *)
  Definition special_decomposition :
    forall beh (c p:I.program),
      I.complete2 c p ->
      let ip := compile (I.link c p) in
      program_behaves (T.sem ip) beh ->
      program_behaves (T.psem (I.get_interface c) ip) beh.
  Proof.
    intros b c p Hcomp tp H.
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
    forall (beht:program_behavior) (c p:I.program),
      I.complete2 c p ->
      let ip := I.link c p in
      program_behaves (T.psem (I.get_interface c) (compile ip)) beht ->
      exists behi,
      program_behaves (I.psem (I.get_interface c) p) behi /\
      behavior_improves_p behi beht (I.get_interface p).
End MPC.

(* Software Fault Isolation compiler *)
Module SFIC <: IT.
  Module T := SFI.
  
  Axiom compile : I.program -> T.program.
  Axiom compile_spec:
    forall (p:I.program),
      I.complete p -> T.valid (compile p) /\
                   I.get_interface p = T.get_interface (compile p).

  (* Axiom partialize: interface -> T.program -> T.program. *)
  (* Axiom partialize_spec: *)
  (*   forall psi (p:T.program), *)
  (*     T.valid p -> *)
  (*     contained psi (T.get_interface p) -> *)
  (*     (T.get_interface p) = (T.get_interface (partialize psi p))++psi. *)

  Axiom sem_spec:
    forall p b, program_behaves (T.sem p) b -> not_wrong b.

  (* there is no generic decomposition, we need to prove *)
  (*       special_decomposition *)
  Axiom special_decomposition :
    forall beh (c p:I.program),
      I.complete2 c p ->
      let ip := compile (I.link c p) in
      program_behaves (T.sem ip) beh ->
      program_behaves (T.psem (I.get_interface c) ip) beh.
    
  Axiom special_compiler_correctness:
    forall (beht:program_behavior) (c p:I.program),
      I.complete2 c p ->
      let ip := I.link c p in
      program_behaves (T.psem (I.get_interface c) (compile ip)) beht ->
      exists behi,
      program_behaves (I.psem (I.get_interface c) p) behi /\
      behavior_improves_p behi beht (I.get_interface p).
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

  Definition RC_DC :=
    forall (c:I.program) (P:S.program) (beht:program_behavior),
      I.valid c ->
      S.valid P ->
      icomplete2 (I.get_interface c) (S.get_interface P) ->
      program_behaves (IT.T.sem (IT.compile (I.link c (SI.compile P)))) beht
      ->
      exists C behs,
        S.valid C /\
        S.get_interface C = I.get_interface c /\
        program_behaves (S.sem (S.link C P)) behs /\
        behavior_improves_p behs beht (S.get_interface P).

  Theorem robust_compilation_dynamic_compromise : RC_DC.
  Proof.
    intros c P bt Hvalc HvalP Hicompl Hsem.
    destruct (SI.compile_spec P HvalP) as [Hvalcomp Hif] .
    apply IT.special_decomposition in Hsem.
    eapply IT.special_compiler_correctness in Hsem as [bi [HPI HimpIT]].
    apply SI.partial_compiler_correctness in HPI as [bs [HPS HimpSI]].
    apply S.definability in HPS as [C [HvalC [HCint HCS]]].
    exists C. exists bs.
    repeat split; eauto.
    rewrite <- Hif in HimpIT.
    specialize (behavior_improves_p_trans bs bi bt (S.get_interface P) HimpSI HimpIT) as HimpST.
    auto.
    auto.
    auto.
    auto.
    auto.
    unfold I.complete2. rewrite <- Hif. repeat split; auto.
    unfold I.complete2. rewrite <- Hif. repeat split; auto.
Qed.


  (* This property is strictly weaker than the above, but has the
     advantage of not mentioning the intermediate language *)
  Definition robust_compilation_static_compromise_weaker :=
    forall (Q P:S.program) (beht:program_behavior),
      S.complete2 Q P ->
      program_behaves (IT.T.sem (IT.compile (I.link (SI.compile Q) (SI.compile P)))) beht ->
      exists C behs,
        S.valid C /\
        S.get_interface C = S.get_interface Q /\
        program_behaves (S.sem (S.link C P)) behs /\
        behavior_improves_p behs beht (S.get_interface P).

  Corollary robust_compilation_corrolary :
    RC_DC ->
    robust_compilation_static_compromise_weaker.
  Proof.
    intros RC Q P b Hcompl H2.
    specialize (RC (SI.compile Q) P b).
    assert (Hcompl2 := Hcompl).
    destruct Hcompl2 as [HvalQ [HvalP Hicompl]].
    destruct (SI.compile_spec Q).
    auto.
    rewrite <- H0 in RC.
    apply (RC H HvalP Hicompl H2).
  Qed.
End Main.

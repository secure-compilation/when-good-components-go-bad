Require Import Smallstep.
Require Import Behavior.
Require Import Coq.Lists.List.

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
Variable id : Type.
Definition interface := list id.
(* complete program has a complete interface *)
Variable icomplete : interface -> Prop.
Definition icomplete2 (i1 i2:interface) := icomplete (i1++i2).
Variable turn : program_behavior -> interface -> Prop.


(* 
   The languages.
 *)

(* Signature of basic things expected in a language *)
Module Type Lang.
  (* Type of programs, complete or partial *)
  Parameter program : Type.

  Parameter get_interface: program -> interface.

  (* checks if a program has a complete interface *)
  Parameter complete: program -> Prop.
  (* checks if two programs linked together form a complete program *)
  Parameter complete2: program -> program -> Prop.

  (* complete semantics: takes a complete program *)
  Parameter sem: program -> semantics.

  (* partial semantics: takes a program and a matching interface.
     The interface of the program together with the matching interface
     is complete. *)
  Parameter psem: program -> interface -> semantics.
End Lang.

(* Every language is a subtype of Lang and implements its signature *)
(* Note: nothing is really implemented, we just give type signatures *)

(* Target *)
Module T <: Lang.
  Variable program : Type.
  Variable get_interface: program -> interface.
  Definition complete (p:program) := icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := icomplete2 (get_interface p1) (get_interface p2).
  Variable sem: program -> semantics.
  Variable psem: program -> interface -> semantics.
End T.

(* Intermediate *)
Module I <: Lang.
  Variable program : Type.
  Variable get_interface: program -> interface.
  Definition complete (p:program) := icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := icomplete2 (get_interface p1) (get_interface p2).
  Variable sem: program -> semantics.
  Variable psem: program -> interface -> semantics.

  (* linking of two partial programs, returns a complete program *)
  Variable link: program -> program -> program.
  
  Definition fully_defined (prg:program) :=
    forall (ctx:program) (beh:program_behavior),
      complete2 ctx prg ->
      program_behaves (sem (link ctx prg)) beh ->
      turn beh (get_interface prg) ->
      not_wrong beh.
End I.

(* Source *)
Module S <: Lang.
  Variable program : Type.
  Variable get_interface: program -> interface.
  Definition complete (p:program) := icomplete (get_interface p).
  Definition complete2 (p1 p2:program) := icomplete2 (get_interface p1) (get_interface p2).
  Variable link: program -> program -> program.
  Variable sem: program -> semantics.
  Variable psem: program -> interface -> semantics.

  Definition fully_defined (prg:program) :=
    forall (ctx:program) (beh:program_behavior),
      complete2 ctx prg ->
      program_behaves (sem (link ctx prg)) beh ->
      turn beh (get_interface prg) ->
      not_wrong beh.
        
  Hypothesis definability :
    forall beh (prg:program) psi,
      icomplete2 (get_interface prg) psi ->
      program_behaves (psem prg psi) beh ->
      exists (ctx:program),
        program_behaves (sem (link ctx prg)) beh.
End S.



(* This module takes a high language L1 and a low one L2 and produces
   a compiler from L1 to L2 and some properties *)
Module Compiler (L1 L2: Lang).
  Variable compile : L1.program -> L2.program.

  (* probably a corollary of partial compiler correctness *)
  Hypothesis compiler_correctness :
    forall beh (p:L1.program),
      program_behaves (L2.sem (compile p)) beh ->
      program_behaves (L1.sem p) beh.

  Hypothesis compiler_interfaces:
  forall (p1:L1.program),
    L1.get_interface p1 = L2.get_interface (compile p1).
End Compiler.

Module IT := Compiler I T.
Module SI := Compiler S I.


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
    icomplete2 (S.get_interface P) (I.get_interface c) ->
    S.fully_defined P ->
    program_behaves (T.sem (IT.compile (I.link c (SI.compile P)))) beh ->
    exists C, program_behaves (S.sem (S.link C P)) beh.


Definition robust_compilation_static_compromise_corollary :=
  forall (Q P:S.program) (beh:program_behavior),
    S.complete2 P Q ->
    S.fully_defined P ->
    program_behaves (T.sem (IT.compile (SI.compile (S.link Q P)))) beh ->
    exists C, program_behaves (S.sem (S.link C P)) beh.

(* This is too syntactic, it should be stated in terms of equivalent behaviors *)
Hypothesis Sseparate_compilation:
  forall (P Q: S.program),
    SI.compile (S.link P Q) = I.link (SI.compile P) (SI.compile Q).

Corollary robust_compilation_corrolary :
  robust_compilation_static_compromise ->
  robust_compilation_static_compromise_corollary.
Proof.
  intros RC Q P b H1 H2 H3. specialize (RC (SI.compile Q) P b).
  apply RC.
  rewrite <- SI.compiler_interfaces with (p1:=Q).
  auto.
  auto.
  rewrite Sseparate_compilation in H3.
  auto.
Qed.


(* Extra ingredients needed for the proof. *)

Hypothesis SIpcompiler_correctness :
  forall beh (p:S.program) (psi:interface),
    S.fully_defined p ->
    program_behaves (I.psem (SI.compile p) psi) beh ->
    program_behaves (S.psem p psi) beh.

(* Takes a complete program and produces a partial one -- CH: potentially drop *)
Variable Tpartialize: T.program -> interface -> T.program.

Hypothesis Tdecomposition:
  forall beh (c p:I.program),
    program_behaves (T.sem (IT.compile (I.link c p))) beh ->
    program_behaves (T.psem (Tpartialize (IT.compile (I.link c p)) (I.get_interface c)) (I.get_interface c)) beh.

Hypothesis ITspecial_pcompiler_correctness:
  forall beh (c p:I.program),
    I.fully_defined p ->
    program_behaves (T.psem (Tpartialize (IT.compile (I.link c p)) (I.get_interface c)) (I.get_interface c)) beh
    ->
    program_behaves (I.psem p (I.get_interface c)) beh.

Hypothesis Idecomposition:
  forall beh (c p:I.program),
    program_behaves (I.sem (I.link c p)) beh ->
    program_behaves (I.psem p (I.get_interface c)) beh.

(* Lemma FD_preservation: *)
(*   forall (P:S.program), *)
(*     S.fully_defined P -> I.fully_defined (SI.compile P). *)
(* Proof. *)
(*   unfold I.fully_defined. *)
(*   unfold S.fully_defined. *)
(*   intros P FD c b Hcomplete H1 Hturn.  *)
(*   apply Idecomposition in H1. *)
(*   apply SIpcompiler_correctness in H1. *)
(*   destruct (S.definability b P (I.get_interface c) H1) as [c2 H]. *)
(*   unfold I.complete2 in Hcomplete. *)
(*   rewrite <- SI.compiler_interfaces in Hcomplete. *)
(*   unfold S.complete2 in FD. *)
(*   apply (FD c2 b Hcomplete). *)
(*   unfold S.fully_defined in FD. *)
(*   specialize (FD (compile )) *)
(*   rewrite <- Sseparate_compilation in H1. *)
(*   apply SI.compiler_correctness in H1. *)
(*   apply (FD c). *)
  
Theorem proof_rc_static : robust_compilation_static_compromise.
Proof.
  unfold robust_compilation_static_compromise.
  intros c P b Hsplit HFD H.
  apply Tdecomposition in H.
  apply ITspecial_pcompiler_correctness in H.
  apply SIpcompiler_correctness in H.
  apply S.definability in H.
  auto. assumption. admit. (* probably corollary of SI[p?]compiler *)
Admitted.

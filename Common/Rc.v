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
Variable complete : interface -> Prop.
Variable turn : program_behavior -> interface -> Prop.


(* 
   The languages.
 *)

(* Signature of basic things expected in a language *)
Module Type Lang.
  (* Type of programs, complete or partial *)
  Parameter program : Type.

  Parameter get_interface: program -> interface.

  (* complete semantics: takes a complete program *)
  Parameter sem: program -> semantics.

  (* partial semantics: takes a program and a matching interface.
     The interface of the program together with the matching interface
     is complete.*)
  Parameter psem: program -> interface -> semantics.
End Lang.

(* Every language is a subtype of Lang and implements its signature *)
(* Note: nothing is really implemented, we just give type signatures *)

(* Target *)
Module T <: Lang.
  Variable program : Type.
  Variable get_interface: program -> interface.
  Variable sem: program -> semantics.
  Variable psem: program -> interface -> semantics.
End T.

(* Intermediate *)
Module I <: Lang.
  Variable program : Type.
  Variable get_interface: program -> interface.
  Variable sem: program -> semantics.
  Variable psem: program -> interface -> semantics.

  (* linking of two partial programs, returns a complete program *)
  Variable link: program -> program -> program.

  Definition fully_defined (prg:program) :=
    forall (ctx:program) (beh:program_behavior),
      program_behaves (sem (link ctx prg)) beh ->
      turn beh (get_interface prg) ->
      not_wrong beh.
End I.

(* Source *)
Module S <: Lang.
  Variable program : Type.
  Variable get_interface: program -> interface.
  Variable sem: program -> semantics.
  Variable psem: program -> interface -> semantics.

  Variable link: program -> program -> program.

  Definition fully_defined (prg:program) :=
    forall (ctx:program) (beh:program_behavior),
      program_behaves (sem (link ctx prg)) beh ->
      turn beh (get_interface prg) ->
      not_wrong beh.
        
  Hypothesis definability :
    forall beh (prg:program) psi,
      program_behaves (psem prg psi) beh ->
      exists (ctx:program),
        program_behaves (sem (link ctx prg)) beh.
End S.


(* This module takes a high language L1 and a low one L2 and produces
   a compiler from L1 to L2 and some properties *)
Module Compiler (L1 L2: Lang).
  (* checks if two programs linked together form a complete program *)
  Definition vsplit (p1: L1.program) (p2: L2.program) :=
    complete ((L2.get_interface p2)++(L1.get_interface p1)).

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
    SI.vsplit P c ->
    S.fully_defined P ->
    program_behaves (T.sem (IT.compile (I.link c (SI.compile P)))) beh ->
    exists C, program_behaves (S.sem (S.link C P)) beh.


Definition robust_compilation_static_compromise_corollary :=
  forall (Q P:S.program) (beh:program_behavior),
    complete (S.get_interface Q ++ S.get_interface P) ->
    S.fully_defined P ->
    program_behaves (T.sem (IT.compile (SI.compile (S.link Q P)))) beh ->
    exists C, program_behaves (S.sem (S.link C P)) beh.

Corollary robust_compilation_corrolary :
  robust_compilation_static_compromise ->
  robust_compilation_static_compromise_corollary.
Proof.
  intros RC Q P b H1 H2 H3. specialize (RC (SI.compile Q) P b).
Admitted.


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




(* Alternative proof which should be broken but is not because
definitions too approximate *)

Hypothesis Idecomposition:
  forall beh (ctx:I.program) (prg:I.program),
    complete ((I.get_interface ctx)++(I.get_interface prg)) ->
    program_behaves (I.sem (I.link ctx prg)) beh ->
    program_behaves (I.psem prg (I.get_interface ctx)) beh.

(* this proof doesn't assume T.decomposition but it is weaker 
   and has problems with UB in CI *)
Theorem bad_proof_rc_static : robust_compilation_static_compromise.
Proof.
  unfold robust_compilation_static_compromise.
  intros c P b Hsplit HFD H.
  apply IT.compiler_correctness in H. 
  apply Idecomposition in H.
  apply SIpcompiler_correctness with (psi:=I.get_interface c) in H. 
  apply S.definability in H.
  auto.
  unfold SI.vsplit in Hsplit.
  rewrite SI.compiler_interfaces in Hsplit.
  auto. admit.
Admitted.

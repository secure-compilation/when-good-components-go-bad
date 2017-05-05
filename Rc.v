Require Import Smallstep.
Require Import Behavior.

(* 
   Full proof of robust compilation relying on 
   - target decomposition,
   - compiler correctness and 
   - source definability
 *)

(* TODO 
  - res monad for compile and link
  - proof some stuff about linking 
 link should check that:
   - there is no intersection between the interfaces of p and c
   - they provide each other's imports
*) 

(* Target language *)
Module T.
  Variable cp : Type.           (* complete program *)
  Variable pp : Type.           (* partial  program *)

  Variable link: pp -> pp -> cp.
  Variable sem: cp -> semantics.
  Variable psem: pp -> semantics.

  Hypothesis decomposition:
    forall beh (ctx:pp) (prg:pp),
      program_behaves (sem (link ctx prg)) beh ->
      program_behaves (psem prg) beh.
End T.

(* Intermediate language *)
(* We don't really need the complete semantic for the intermediate language *)
Module I.
  (* Variable cp : Type. *)
  Variable pp : Type.

  (* Variable link: p -> p -> c. *)
  (* Variable sem: c -> semantics. *)
  Variable psem: pp -> semantics.
End I.

(* Source language *)
Module S.
  Variable cp : Type.
  Variable pp : Type.

  Variable link: pp -> pp -> cp.
  Variable sem: cp -> semantics.
  Variable psem: pp -> semantics.

  (* doesn't go wrong during prg or ctx turn *)
  Definition fully_defined (P:pp) :=
    forall (C:pp) (beh:program_behavior),
      program_behaves (sem (link C P)) beh ->
      not_wrong beh.
  (* is this better? *)
  Definition fully_defined2 (P:pp) :=
    forall (beh:program_behavior),
      program_behaves (psem P) beh ->
      not_wrong beh.

  Hypothesis definability:
    forall beh (prg:pp),
      program_behaves (psem prg) beh ->
      exists (ctx:pp),
        fully_defined ctx ->
        program_behaves (sem (link ctx prg)) beh.
End S.

Variable compileSI : S.pp -> I.pp.
Hypothesis compiler_correctnessSI : 
  forall beh sp,
    program_behaves (I.psem (compileSI sp)) beh ->
    program_behaves (S.psem sp) beh.


Variable compileIT : I.pp -> T.pp.
Hypothesis compiler_correctnessIT : 
  forall beh ip,
    program_behaves (T.psem (compileIT ip)) beh ->
    program_behaves (I.psem ip) beh.


Definition compile : S.pp -> T.pp :=
  fun p => compileIT (compileSI p).
Lemma compiler_correctness : 
  forall beh sp,
    program_behaves (T.psem (compile sp)) beh ->
    program_behaves (S.psem sp) beh.
Proof.
  intros b sp H.
  apply compiler_correctnessSI.
  apply compiler_correctnessIT.
  auto.
Qed.

Definition robust_compilation_for_unsafe_languages:
  forall (c:T.pp) (P:S.pp) (beh:program_behavior),
    S.fully_defined P ->
    program_behaves (T.sem (T.link c (compile P))) beh ->
    exists C, S.fully_defined C ->
              program_behaves (S.sem (S.link C P)) beh.
Proof.
intros c P beh HFD H.
apply T.decomposition in H.
apply compiler_correctness in H.
apply S.definability in H.
auto.
Qed.

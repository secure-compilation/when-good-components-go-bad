Require Import Common.Smallstep.
Require Import Common.Behavior.

(* 
   Full proof of robust compilation relying on 
   - target decomposition,
   - compiler correctness and 
   - source definability
 *)

(* TODO 
  - notion of turn
  - Define how linking merges programs 
  - res monad for compile and link
  - proof some stuff about linking 
 link should check that:
   - there is no intersection between the interfaces of p and c
   - they provide each other's imports
 *)

Variable psi : Type.
Variable Cid : Type.
Variable turn : program_behavior -> Cid.
Variable closed : psi -> psi -> Prop.

(* Target language *)
Module T.
  Variable p : Type.           (* partial  program *)
  
  Variable link: p -> p -> p.
  Variable sem: p -> semantics.
  Variable psem: p -> psi -> semantics.

  (* Hypothesis decomposition: *)
  (*   forall beh (ctx:p) (prg:p), *)
  (*     program_behaves (sem (link ctx prg)) beh -> *)
  (*     program_behaves (psem prg) beh. *)
End T.

(* Intermediate language *)
(* We don't really need the complete semantic for the intermediate language *)
Module I.
  Variable p : Type.

  (* Variable link: p -> p -> p. *)
  (* Variable sem: p -> Pid -> semantics. *)
  Variable psem: p -> psi -> semantics.
End I.

(* Source language *)
Module S.
  Variable p : Type.

  Variable link: p -> p -> p.
  Variable sem: p -> semantics.
  Variable psem: p -> psi -> semantics.

  Definition fully_defined (prg:p) :=
    forall (beh:program_behavior),
      program_behaves (sem prg) beh ->
      turn beh = id /\ In Cid prg ->
      not_wrong beh.
        
  (* Hypothesis definability : *)
  (*   forall beh (prg:p), *)
  (*     program_behaves (psem prg) beh -> *)
  (*     exists (ctx:p), *)
  (*       program_behaves (sem (link ctx prg)) beh. *)
End S.

Variable compileSI : S.p -> I.p.
(* Hypothesis compiler_correctnessSI :  *)
(*   forall beh sp, *)
(*     program_behaves (I.psem (compileSI sp)) beh -> *)
(*     program_behaves (S.psem sp) beh. *)


Variable compileIT : I.p -> T.p.
(* Hypothesis compiler_correctnessIT :  *)
(*   forall beh ip, *)
(*     program_behaves (T.psem (compileIT ip)) beh -> *)
(*     program_behaves (I.psem ip) beh. *)


Definition compile : S.p -> T.p :=
  fun p => compileIT (compileSI p).
(* Lemma compiler_correctness :  *)
(*   forall beh sp, *)
(*     program_behaves (T.psem (compile sp)) beh -> *)
(*     program_behaves (S.psem sp) beh. *)
(* Proof. *)
(*   intros b sp H. *)
(*   apply compiler_correctnessSI. *)
(*   apply compiler_correctnessIT. *)
(*   auto. *)
(* Qed. *)


(* RC static compromise *)
Definition robust_compilation_static_compromise:=
  forall (c:T.p) (P:S.p) (beh:program_behavior),
    S.fully_defined P ->
    program_behaves (T.sem (T.link c (compile P))) beh ->
    exists C, program_behaves (S.sem (S.link C P)) beh.



(* RC_DC': *)
(* c[P↓] ⇓ b₁  ⇒  ∃C. C fully defined ∧ C[P] ⇓ b₂ ∧ *)
(*                    (b₁ = b₂ ∨ ∃b', b", b₁ = b';b" ∧ b₂ = b';UNDEF) *)



(* Definition robust_compilation_for_unsafe_languages: *)
(*   forall (c:T.p) (P:S.p) (beh:program_behavior), *)
(*     program_behaves (T.sem (T.link c (compile P))) beh -> *)
(*     exists C, S.fully_defined C -> *)
(*               program_behaves (S.sem (S.link C P)) beh. *)
(* Proof. *)
(*   intros c P beh H. *)
(*   apply T.decomposition in H. *)
(*   apply compiler_correctness in H. *)
(*   apply S.definability in H. *)
(*   auto. *)
(* Qed. *)



(* RC_DC:
   c[P↓] ⇓ beht  ⇒  ∃C. C[P] ⇓ behs ∧
                    (beht = behs ∨ ∃t, prefix t beht ∧ 
                                       behs = goeswrong(t) /\ 
                                       turn t = P) 
*)
Definition robust_compilation_dynamic_compromise:
  forall (c:T.p) (P:S.p) (beht behs:program_behavior),
    program_behaves (T.sem (T.link c (compile P))) beht ->
    exists C, program_behaves (S.sem (S.link C P)) behs /\
              behavior_improves behs beht /\
              turn behs P.
Proof.
  intros c P b1 b2 H.
  apply T.decomposition in H.
  apply compiler_correctness in H.
  apply S.definability in H.
  auto.
Qed.




(* RC_DC+MD₁: ⋈(C1↓,...,Cn↓)⇓b ⇒ P(Cs,[],b) *)

(* P₁(Cs,As,b) = ⋈(Cs,As)⇓b *)
(*               ∨ ∃b₁b₂=b,Cᵢ. ⋈(Cs,As)⇓b₁;UNDEF in Cᵢ *)
(*                             ∧ ∃Aᵢ. P₁(Cs/Cᵢ,As∪{Aᵢ},b) *)



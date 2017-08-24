Require Import Coq.Lists.List.
Require Import FunctionalExtensionality.

Class Monad (M: Type -> Type) := {
  ret : forall {A}, A -> M A;
  bind : forall {A B}, M A -> (A -> M B) -> M B
}.

Hint Unfold ret.
Hint Unfold bind.

Class MonadLaws M `{Monad M} := {
  m_left_identity :
    forall A B (a: A) (f: A -> M B),
      bind (ret a) f = f a;
  m_right_identity :
    forall A (m: M A),
      bind m ret = m;
  m_associativity :
    forall A B C (m: M A) (f: A -> M B) (g: B -> M C),
      bind (bind m f) g = bind m (fun x => bind (f x) g) 
}.

(** Option Monad **)

Instance option_monad : Monad option := {
 ret A x :=
   Some x;
 bind A B x f :=
   match x with
   | Some y => f y
   | None => None
   end
}.

Lemma option_monad_left_id:
  forall A B (a: A) (f: A -> option B),
    bind (ret a) f = f a.
Proof.
  auto.
Qed.

Lemma option_monad_right_id:
  forall A (m: option A),
    bind m ret = m.
Proof.
  intros.
  destruct m; auto.
Qed.

Lemma option_monad_associativity:
  forall A B C (m: option A) (f: A -> option B) (g: B -> option C),
    bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  intros.
  destruct m; auto.
Qed.

Instance option_monad_laws : MonadLaws option := {
  m_left_identity := option_monad_left_id;
  m_right_identity := option_monad_right_id;
  m_associativity := option_monad_associativity
}.

(** State Monad **)

Definition ST (S A: Type) := S -> A * S.

Instance state_monad {S} : Monad (ST S) := {
  ret A x :=
    fun s => (x, s);
  bind A B s f :=
    fun x => let '(x', s') := s x in
          (f x') s'
}.

Section StateMonad.
  Variable S: Type.

  Definition ST_get : ST S S :=
    fun s => (s, s).

  Definition ST_put (s: S) : ST S unit :=
    fun _ => (tt, s).

  Definition ST_modify (f: S -> S) : ST S unit :=
    fun s => (tt, f s).

  Definition ST_run {A} (m: ST S A) (s: S) : A * S :=
    m s.

  Lemma state_monad_left_id:
    forall A B (a: A) (f: A -> ST S B),
      bind (ret a) f = f a.
  Proof.
    auto.
  Qed.

  Lemma state_monad_right_id:
    forall A (m: ST S A),
      bind m ret = m.
  Proof.
    intros.
    unfold ret, bind. simpl.
    extensionality x.
    destruct (m x); auto.
  Qed.

  Lemma state_monad_associativity:
    forall A B C (m: ST S A) (f: A -> ST S B) (g: B -> ST S C),
      bind (bind m f) g = bind m (fun x => bind (f x) g).
  Proof.
    intros.
    unfold ret, bind. simpl.
    extensionality x.
    destruct m; auto.
  Qed.
End StateMonad.

Instance state_monad_laws {S} : MonadLaws (ST S) := {
  m_left_identity := state_monad_left_id S;
  m_right_identity := state_monad_right_id S;
  m_associativity := state_monad_associativity S
}.

(** List Monad **)

Instance list_monad : Monad list := {
  ret A x := x :: nil;
  bind A B m f := concat (map f m)
}.

Lemma list_monad_left_id:
  forall A B (x: A) (f: A -> list B),
    bind (ret x) f = f x.
Proof.
  intros.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma list_monad_right_id:
  forall A (m: list A),
    bind m ret = m.
Proof.
  intros.
  induction m; auto.
  - simpl.
    replace (a :: m) with (a :: bind m ret)
      by (rewrite IHm; reflexivity).
    reflexivity.
Qed.

Lemma list_monad_associativity:
  forall A B C (m: list A) (f: A -> list B) (g: B -> list C),
    bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  intros.
  induction m; auto.
  - simpl in *.
    rewrite map_app, concat_app, IHm.
    reflexivity.
Qed.

Instance list_monad_laws : MonadLaws list := {
  m_left_identity := list_monad_left_id;
  m_right_identity := list_monad_right_id;
  m_associativity := list_monad_associativity
}.

(* Notations *)

Module MonadNotations.

Notation "'do' X <- A ; B" := (bind A (fun X:_ => B))
  (at level 200, X ident, A at level 100, B at level 200)
  : monad_scope.

Notation "'do!' A ; B" := (bind A (fun _ => B))
  (at level 200, A at level 100, B at level 200)
  : monad_scope.

Notation "'do' ( X , Y ) <- A ; B" :=
  (bind A (fun x:_ => let '(X,Y) := x in B))
  (at level 200, X ident, A at level 100, B at level 200)
  : monad_scope.

Notation "'do' ( X , Y , Z ) <- A ; B" :=
  (bind A (fun x:_ => let '(X,Y,Z) := x in B))
  (at level 200, X ident, A at level 100, B at level 200, Z at level 200)
  : monad_scope.

End MonadNotations.
(* This is a copy of the file in S2I. 
If I don't make any changes it should be moved in  Lib. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Export Lib.Monads.

Require Import FunctionalExtensionality.

(* the compilation monad *)

Module Comp.
  Section Def.
    Variable env: Type.

    Definition t (res: Type) := env -> option (res * env).

    Definition ret A (x:A) := fun (s:env) => Some (x, s).

    Definition bind A B (s: t A) (f: A -> t B) :=
      fun x => match s x with
            | Some (x',s') => (f x') s'
            | None => None
            end.

    Definition get : t env :=
      fun s => Some (s, s).

    Definition put (s: env) : t unit :=
      fun _ => Some (tt, s).

    Definition modify (f: env -> env) : t unit :=
      fun s => Some (tt, f s).

    Definition lift {A} (x: option A) : t A :=
      fun s => match x with
            | None => None
            | Some v => Some (v, s)
            end.

    Definition fail {A} : t A :=
      fun _ => None.

    Definition run {A} (s: env) (m: t A) : option A :=
      match m s with
      | None => None
      | Some (v,s') => Some v
      end.
  End Def.
End Comp.

Instance compilation_monad {env} : Monad (Comp.t env) := {
  ret := Comp.ret env;
  bind := Comp.bind env
}.

Section CompMonadLaws.
  Variable env: Type.
  
  Lemma comp_monad_left_id:
    forall res1 res2 (e: res1) (f: res1 -> Comp.t env res2),
      bind (ret e) f = f e.
  Proof.
    auto.
  Qed.

  Lemma comp_monad_right_id:
    forall res (m: Comp.t env res),
      bind m ret = m.
  Proof.
    intros.
    unfold ret, bind. simpl.
    unfold Comp.ret, Comp.bind.
    extensionality x.
    destruct (m x); auto.
    destruct p. auto.
  Qed.

  Lemma comp_monad_associativity:
    forall res1 res2 res3 (m: Comp.t env res1)
      (f: res1 -> Comp.t env res2) (g: res2 -> Comp.t env res3),
      bind (bind m f) g = bind m (fun x => bind (f x) g).
  Proof.
    intros.
    unfold ret, bind. simpl.
    unfold Comp.ret, Comp.bind.
    extensionality x.
    destruct m; auto.
    destruct p. destruct (f r e); auto.
  Qed.
End CompMonadLaws.

Instance comp_monad_laws {env} : MonadLaws (Comp.t env) := {
  m_left_identity := comp_monad_left_id env;
  m_right_identity := comp_monad_right_id env;
  m_associativity := comp_monad_associativity env
}.
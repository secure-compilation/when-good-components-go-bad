
Require Export Lib.Monads.
Require Import Coq.Strings.String.

Require Import FunctionalExtensionality.
Require Import CompEitherMonad.

Module CompStateMonad.
  Section Def.
    Variable st: Type.

    Definition t (res: Type) := st -> (@CompEither res) * st.

    Definition ret (A:Type) (x:A) : (t A)
      := fun (s:st) => (Right x,s).

    Definition bind A B (s: t A) (f: A -> t B) :=
      fun x => match s x with
            | (Right x',s') => (f x') s'
            | (Left msg err, s') => (Left msg err, s')
            end.

    Definition get : t st :=
      fun s => (Right s, s).

    Definition put (s: st) : t unit :=
      fun _ =>  (Right tt, s).

    Definition modify (f: st -> st) : t unit :=
      fun s => (Right tt, f s).

    Definition lift {A} (x: option A) (msg : string) (err : CompilerError) : t A :=
      fun s => match x with
            | None  => (Left msg NoInfo, s)
            | Some v => (Right v, s)
            end.
    
    Definition fail {A} (msg : string) (err : CompilerError): t A :=
      fun s => (Left msg err, s).

    Definition run {A} (s: st) (m: t A) : CompEither :=
      match m s with
      | (Left msg err,_) => Left msg err
      | (Right v,s') => Right v
      end.
      
  End Def.
End CompStateMonad.

Instance state_monad {st} : Monad (CompStateMonad.t st) := {
  ret := CompStateMonad.ret st;
  bind := CompStateMonad.bind st
}.

Section CompStateMonadLaws.
  Variable st: Type.
  
  Lemma state_monad_left_id:
    forall res1 res2 (e: res1) (f: res1 -> CompStateMonad.t st res2),
      bind (ret e) f = f e.
  Proof.
    auto.
  Qed.

  Lemma state_monad_right_id:
    forall res (m: CompStateMonad.t st res),
      bind m ret = m.
  Proof.
    intros.
    unfold ret, bind. simpl.
    unfold CompStateMonad.ret, CompStateMonad.bind.
    extensionality x.
    destruct (m x); auto.
    destruct c. auto. reflexivity. 
  Qed.

  Lemma state_monad_associativity:
    forall res1 res2 res3 (m: CompStateMonad.t st res1)
      (f: res1 -> CompStateMonad.t st res2) (g: res2 -> CompStateMonad.t st res3),
      bind (bind m f) g = bind m (fun x => bind (f x) g).
  Proof.
    intros.
    unfold ret, bind. simpl.
    unfold CompStateMonad.ret, CompStateMonad.bind.
    extensionality x.
    destruct m; auto.
    destruct c. destruct (f r s); auto. reflexivity.
  Qed.
End CompStateMonadLaws.

Instance state_monad_laws {st} : MonadLaws (CompStateMonad.t st) := {
  m_left_identity := state_monad_left_id st;
  m_right_identity := state_monad_right_id st;
  m_associativity := state_monad_associativity st
}.
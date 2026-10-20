From mathcomp Require Import ssreflect seq ssrfun.

Notation "f ∘ g" := (f \o g) (at level 30).

Lemma obind_inv A B (f : A -> option B) (a : option A) (b : B) :
  obind f a = Some b -> exists a', a = Some a' /\ f a' = Some b.
Proof.
  destruct a as [a'|]; simpl; solve [eauto | discriminate].
Qed.

Theorem obind_assoc : forall A B C
                             (mx : option A)
                             (my : A -> option B)
                             (mz : B -> option C),
  obind (obind mz \o my) mx = obind mz (obind my mx).
Proof.
  intros A B C mx my mz.
  destruct mx as [x|]; [destruct (my x) as [y|]|]; reflexivity.
Qed.

Module DoNotation.

Import ssrfun.

Notation "'do!' X <- A ; B" :=
  (obind (fun X => B) (A))
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do!' X : T <- A ; B" :=
  (obind (fun X : T => B) (A))
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do!' 'guard' cond ; rest" :=
  (if cond then rest else None)
  (at level 200, cond at level 100, rest at level 200).

Notation "'do!' 'guard?' ocond ; rest" :=
  match ocond with
    | Some true         => rest
    | Some false | None => None
  end
  (at level 200, ocond at level 100, rest at level 200).

End DoNotation.

Import DoNotation.

Variant tag :=
  | Ret: nat -> tag
  | InternalJump: tag
  | Other: tag
  | Invalidated: tag
.

Definition memory := nat -> option (nat * tag).


Axiom is_code: tag -> Prop.
Axiom is_relevant: nat -> tag -> Prop.

Definition address_correctness c w t (mem: memory) :=
  match t with
  | Ret _ | InternalJump => exists v, mem w = Some v /\ (is_relevant c (snd v) -> is_code (snd v))
  | Other | Invalidated => True
  end.

Record state :=
  { pc: nat * tag;
    regs: nat -> option (nat * tag);
    mem: memory; }
.

Definition memory_address_correctness c (s: state) :=
  forall v w,
    is_relevant c (snd v) ->
    mem s w = Some v ->
    address_correctness c (fst v) (snd v) (mem s).


Axiom cm: nat -> nat.
Axiom pref_filt: nat -> bool.
Axiom domm: memory -> seq nat.
Axiom mem_of_seq: seq (nat * (nat * tag))  -> memory.
Axiom unionm: memory -> memory -> memory.
Axiom updm: (nat -> option (nat * tag)) -> nat -> (nat * tag) -> option (nat -> option (nat * tag)).

Definition isSome {S} (a: option S) := match a with | Some _ => true | None => false end.
Lemma unionmE
     : forall (m1 m2 : memory) (k : nat),
       unionm m1 m2 k = (if isSome (m1 k) then m1 k else m2 k).
Admitted.

Definition syscall_ret := 0.
Definition syscall_arg1 := 1.
Definition ra := 2.
Definition is_jump t := match t with | InternalJump => Some tt | _ => None end.
Definition is_other t := match t with | Other => Some tt | _ => None end.

Definition alloc_fun (st : state) : option state :=
  let current_c := (match (snd (pc st)) with Ret c => c | _ => 0 end) in
  do! ra_val <- regs st ra;
  do! _ <- is_jump (snd ra_val);
  let next_pc := (fst ra_val, snd (pc st)) in
  let prefix := cm current_c in
  let prefix_filter := (fun mw => pref_filt mw) in
  let max_addr := last prefix (filter prefix_filter (domm (mem st))) in
  let atom := (0, Other) in
  do! size <- regs st syscall_arg1;
  do! _ <- is_other (snd size);
  let length := fst size in
  if negb (prefix_filter (max_addr + length + 1)) then
    None
  else
  let bloc := mkseq (fun n => (max_addr + n + 1, atom)) length in
  let mem' := unionm (mem st) (mem_of_seq bloc) in
  do! addr <- (do! x <- ohead bloc;
                 Some (fst x));
  do! regs' <- updm (regs st) syscall_ret (addr, Other);
  Some {| pc := next_pc;
         regs := regs';
         mem := mem'; |}.

  Ltac unfold_match :=
    let a := fresh "a" in
    match goal with
    | H : (match ?cond as _ return _ with _ => _ end) = Some _  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : Some _ = (match ?cond as _ return _ with _ => _ end)  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : (match ?cond as _ return _ with _ => _ end) = None  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : None = (match ?cond as _ return _ with _ => _ end)  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : (match ?cond as _ return _ with _ => _ end) = true  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : true = (match ?cond as _ return _ with _ => _ end)  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : (match ?cond as _ return _ with _ => _ end) = false  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    | H : false = (match ?cond as _ return _ with _ => _ end)  |- _ => try(remember cond as a; destruct a);
                                                                   simpl in H; try (inversion H; done)
    end.

  Ltac unfold_bind :=
    let a := fresh "a" in
    match goal with
    | H : _ = (Option.bind ?f ?v) |- _ => remember v as a; destruct a; simpl in H; try (inversion H; done)
    | H : (Option.bind ?f ?v) = _ |- _ => remember v as a; destruct a; simpl in H; try (inversion H; done)
    | H : match (Option.bind ?f ?v) with _ => _ end |- _ => remember v as a; destruct a; simpl in H; try (inversion H; done)
    end.

  Ltac simplify_some :=
    match goal with
    | H : Some ?a = Some _ |- _ => inversion H; clear H; subst a
    | H : Some (?a, ?b) = Some _ |- _ => inversion H; clear H; try subst a; try subst b
    | H : (?a, ?b) = (_, _) |- _ => inversion H; clear H; try subst a; try subst b
    | H : Some _ = Some ?a |- _ => inversion H; clear H; try subst a
    | H : Some _ = Some (?a, ?b) |- _ => inversion H; clear H; try subst a; try subst b
    | H : (_, _) = (?a, ?b) |- _ => inversion H; clear H; try subst a; try subst b
    end.

  Ltac destruct_unit :=
    match goal with
    | u: unit |- _ => destruct u
    end.

  Ltac unfold_match_misc :=
    let a := fresh "a" in
    match goal with
    | H : _ = (match ?cond as _ return _ with _ => _ end) _  |- _ => try(remember cond as a; destruct a);
                                                                  simpl in H; try (inversion H; done)
    | H : _ = (match ?cond as _ return _ with _ => _ end) _ _  |- _ => try(remember cond as a; destruct a);
                                                                    simpl in H; try (inversion H; done)
    | H : (match ?cond as _ return _ with _ => _ end) _ = _  |- _ => try(remember cond as a; destruct a);
                                                                  simpl in H; try (inversion H; done)
    end.
  Ltac unfold_all :=
    repeat (simpl in *;(simplify_some || unfold_bind || destruct_unit || unfold_match_misc)).

  Lemma mem_of_seq_false: forall v' w s n0 vd t,
           mem_of_seq (mkseq (fun n : nat => (last (cm n0) [seq mw <- domm (mem s) | pref_filt mw] + n + 1, (0, Other))) v') w =
         Some (vd, t) ->
           t <> Other -> False.
  Admitted.

  Lemma alloc_preserves_memory_address_correctness:
    forall c s s',
      memory_address_correctness c s ->
      alloc_fun s = Some s' ->
      memory_address_correctness c s'.
  Proof.
    intros i s s' s_mem_cor alloc d w rel d_eq.
    unfold alloc_fun in *.
    repeat (unfold_all || unfold_match).
    unfold is_jump, is_other in *.
    repeat (unfold_all || unfold_match).
    destruct p as [v tmp]. destruct p0 as [v' tmp']. simpl in *. subst tmp tmp'.
    simpl. destruct d as [vd td]. destruct td.
    destruct snd; simpl; auto.
    all: simpl in *; auto.
    all: rewrite unionmE; rewrite unionmE in d_eq; simpl in *.
    all: remember (mem s w) as cond; simpl in *.
    all:  destruct cond; simpl in *.
    all: try (pose proof (s_mem_cor p w ); simplify_some; simpl in *;
              pose proof (H rel (esym Heqcond)) as [d' [d'eq d'cond]];
              rewrite d'eq; simpl; eauto).
    all: exfalso; clear - d_eq.
    all: eapply mem_of_seq_false; eauto.
    all: congruence.
  Qed.

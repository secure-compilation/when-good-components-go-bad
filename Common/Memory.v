Require Import Common.Definitions.
Require Import Common.Values.

Module Type AbstractComponentMemory.
  Parameter t : Type.

  Parameter prealloc : list (Block.id * nat) -> t.
  Parameter empty : t.
  Parameter reserve_block : t -> t * Block.id.
  Parameter alloc : t -> nat -> t * Block.id.
  Parameter load : t -> Block.id -> Block.offset -> option value.
  Parameter store : t -> Block.id -> Block.offset -> value -> option t.

  Axiom load_after_alloc:
    forall m m' n b,
      alloc m n = (m',b) ->
    forall b' i,
      b' <> b -> load m' b' i = load m b' i.

  Axiom load_after_store:
    forall m m' b i v,
      store m b i v = Some m' ->
    forall b' i',
      ((b' <> b \/ i' <> i) /\ load m' b' i' = load m b' i') \/
      load m' b' i' = Some v.
End AbstractComponentMemory.

Module ComponentMemory : AbstractComponentMemory.
  Definition block := list value.

  Record mem := mkMem {
    content : NMap.t block;
    nextblock : Block.id;
  }.
  Definition t := mem.

  Definition prealloc (bufs: list (Block.id * nat)) : t :=
    let fix prepare m bs :=
        match bs with
        | [] => m
        | (b, size) :: bs' =>
          let chunk := repeat Undef size in
          let m' := {| content := NMap.add b chunk (content m);
                       nextblock := max (1+b) (nextblock m) |} in
          prepare m' bs'
        end
    in prepare {| content := @NMap.empty block;
                  nextblock := 0 |} bufs.

  Definition empty := prealloc [].

  Definition reserve_block (m: t) : t * Block.id :=
    ({| content := content m; nextblock := 1 + nextblock m |},
     nextblock m).

  Definition alloc m (size : nat) : mem * Block.id :=
    let fresh_block := nextblock m in
    let chunk := repeat Undef size in
    ({| content := NMap.add fresh_block chunk (content m);
        nextblock := 1 + nextblock m |},
     fresh_block).

  Definition load m b i : option value :=
    match NMap.find b (content m) with
    | Some chunk =>
      match i with
      | Z.neg _ => None
      | _ => nth_error chunk (Z.to_nat i)
      end
    | None => None
    end.

  Fixpoint block_update data offset val : option block :=
    match data with 
    | [] => None (* store out of bounds *)
    | val' :: rest =>
      match offset with
      | 0 => Some (val :: rest) 
      | S offset' =>
        match block_update rest offset' val with
        | Some rest' => Some (val' :: rest')
        | None       => None (* propagate store out of bounds *)
        end
      end
    end.
  
  Definition store m b i v : option mem :=
    match NMap.find b (content m) with
    | Some chunk =>
      match i with
      | Z.neg _ => None
      | _ => match block_update chunk (Z.to_nat i) v with
            | Some chunk' =>
              Some {| content := NMap.add b chunk' (content m);
                      nextblock := nextblock m |}
            | _ => None
            end
      end
    | None => None
    end.

  Lemma load_after_alloc:
    forall (m m' : mem) (n : nat) b,
      alloc m n = (m',b) ->
    forall b' i,
      b' <> b -> load m' b' i = load m b' i.
  Proof.
    intros m m' n b Halloc b' i Hb'.
    unfold alloc in Halloc. inversion Halloc. subst.
  Admitted.

  Lemma load_after_store:
    forall m m' b i v,
      store m b i v = Some m' ->
    forall b' i',
      ((b' <> b \/ i' <> i) /\ load m' b' i' = load m b' i') \/
      load m' b' i' = Some v.
  Proof.
    intros m m' b i v Hstore b' i'.
    destruct (b =? b') eqn:Hbeqb'.
  Admitted.
End ComponentMemory.

Module Memory.
  Definition t := NMap.t ComponentMemory.t.

  Fixpoint empty (cs: list Component.id) :=
    match cs with
    | [] => @NMap.empty (ComponentMemory.t)
    | c::cs' => NMap.add c ComponentMemory.empty (empty cs')
    end.

  Definition alloc (mem : t) (C : Component.id) (size : nat) : option (t * Pointer.t) :=
    match NMap.find C mem with
    | Some memC =>
      let '(memC', b) := ComponentMemory.alloc memC size in
      Some (NMap.add C memC' mem, (C, b, 0%Z))
    | None => None
    end.

  Definition load (mem : t) (ptr : Pointer.t) : option value :=
    let '(C, b, o) := ptr in
    match NMap.find C mem with
    | Some memC => ComponentMemory.load memC b o
    | None => None
    end.

  Definition store (mem :t) (ptr : Pointer.t) (v : value) : option t :=
    let '(C, b, o) := ptr in
    match NMap.find C mem with
    | Some memC =>
      match ComponentMemory.store memC b o v with
      | Some memC' => Some (NMap.add C memC' mem)
      | None => None
      end
    | None => None
    end.
End Memory.
Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Linking.
Require Import Lib.Extra.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
Require Import Common.Memory.
Require Import Tags.

Module Memory. (* : AbstractComponentMemory.*)
  Definition block := list (tvalue * mem_tag).

  Implicit Types (b : Block.id).

  Record mem := mkMem {
    content : NMap block;
    nextblock : Block.id;
  }.
  Definition t := mem.



  Definition prealloc (bufs: {fmap Block.id -> (Component.id * (nat + list value))}) : t :=
    let init_block x := match x with
                        | (c,inl size) => repeat (tUndef, c) size
                        | (c,inr chunk) => to_tagged_block c chunk
                        end in
    {| content := mapm init_block bufs;
       nextblock := S (fold_left Nat.max (domm bufs) 0) |}.


  Definition prealloc_c C (bufs: {fmap Block.id -> ((nat + list value))}) : t :=
    let init_block x := match x with
                        | inl size => repeat (tUndef, C) size
                        | inr chunk => to_tagged_block C chunk
                        end in
    {| content := mapm init_block bufs;
       nextblock := S (fold_left Nat.max (domm bufs) 0) |}.


  Definition empty :=
    {| content := emptym; nextblock := 0 |}.

  Definition reserve_block (m: t) : t * Block.id :=
    ({| content := content m; nextblock := (1 + nextblock m)%nat |},
     nextblock m).

  Definition alloc (c : Component.id) m (size : nat) : mem * Block.id :=
    let fresh_block := nextblock m in
    let chunk := repeat (tUndef,c) size in
    ({| content := setm (content m) fresh_block chunk;
        nextblock := (1 + nextblock m) |},
     fresh_block).



  Definition load_b m b i : option (tvalue * mem_tag) :=
    match getm (content m) b with
    | Some chunk =>
      if (0 <=? i)%Z then nth_error chunk (Z.to_nat i)
      else None
    | None => None
    end.

  Definition load m ptr : option (tvalue * mem_tag) := load_b m (Pointer.block ptr) (Pointer.offset ptr).

  Definition store_b m b i v : option mem :=
    match getm (content m) b with
    | Some chunk =>
      if (0 <=? i)%Z then
        match list_upd chunk (Z.to_nat i) v with
        | Some chunk' =>
          Some {| content := setm (content m) b chunk';
                  nextblock := nextblock m |}
        | _ => None
        end
      else None
    | None => None
    end.

  Definition store m ptr v : option mem := store_b m (Pointer.block ptr) (Pointer.offset ptr) v.

  Definition domm (m : t) := @domm nat_ordType block (content m).

End Memory.

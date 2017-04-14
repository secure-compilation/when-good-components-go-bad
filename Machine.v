Require Import Common.

Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Structures.OrdersAlt.

Module AbstractMachine.

Module backNat_as_OT := Backport_OT Nat_as_OT.
Module M := FMapAVL.Make backNat_as_OT.
Module P := WProperties_fun Nat_as_OT M.
Module F := P.F.

Module Register.
  Definition data : Type := M.t nat.

  Inductive reg : Set :=
    R_PC | R_ONE | R_COM | R_AUX1 | R_AUX2 | R_RA | R_SP.

  Definition to_nat (r : reg) : nat :=
    match r with
    | R_PC   => 0
    | R_ONE  => 1
    | R_COM  => 2
    | R_AUX1 => 3
    | R_AUX2 => 4
    | R_RA   => 5
    | R_SP   => 6
    end.

  Definition get (r : reg) (regs : data) : nat :=
    match M.find (to_nat r) regs with
    | Some val => val
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => 0
    end.

  Definition set (r : reg) (val : nat) (regs : data) : data :=
    M.add (to_nat r) val regs.
End Register.

Module Memory.
  Definition address := nat.
  Definition data: Type := M.t (list nat).

  Definition get mem C a : option nat :=
    match M.find C mem with
    (* when the address 'a' points outside of memory, we just return 0 *)
    | Some cmem => Some (nth a cmem 0)
    | None => None
    end.

  Fixpoint local_update (a : address) (val : nat) (lmem : list nat) :=
    match lmem with
    | [] =>
      (* extend the memory, since the address points outside of it *)
      (* (we are modeling an infinite memory, hence this extension) *)
      match a with
      | 0 => [val]
      | S a' => 0 :: local_update a' val []
      end
    | val' :: lmem' =>
      match a with
      | 0 => val :: lmem'
      | S a' => val' :: local_update a' val lmem'
      end
    end.

  Definition set mem C a val :=
    match M.find C mem with
    | Some cmem =>
      M.add C (local_update a val cmem) mem
    | None => mem
    end.

  Definition of_component C mem : option (list nat) := M.find C mem.

  Definition inject C cmem (mem : data) := M.add C cmem mem.

  Definition filter (pc : list Component.id) (mem : data) :=
    P.filter (fun C _ => existsb (fun C' => C =? C') pc) mem.

  Definition singleton C cmem : data :=
    M.add C cmem (M.empty (list Memory.address)).

  Lemma get_works_locally :
    forall mem cmem C i,
      of_component C mem = Some cmem ->
      get mem C i = get (singleton C cmem) C i.
  Proof.
    intros.
    unfold singleton, get.
    unfold of_component in H.
    rewrite H. rewrite F.add_eq_o; reflexivity.
  Qed.
End Memory.
 
Inductive binop := Add | Minus | Mul | Eq | Leq.

Inductive instr :=
| Nop    : instr
(* register operations *)
| Const  : nat -> Register.reg -> instr
| Mov    : Register.reg -> Register.reg -> instr
| BinOp  : binop -> Register.reg -> Register.reg -> Register.reg -> instr
(* memory operations *)
| Load   : Register.reg -> Register.reg -> instr
| Store  : Register.reg -> Register.reg -> instr
(* conditional and unconditional jumps *)
| Bnz    : Register.reg -> nat -> instr
| Jump   : Register.reg -> instr
| Jal    : Register.reg -> instr
(* components interaction *)
| Call   : Component.id -> Procedure.id -> instr
| Return : instr
(* termination *)
| Halt   : instr.

Module EncDec.
  (* we assume to have a decoder for our instruction. Later we could try
     to think of a simple representation for instructions and implement
     it for real *)

  Definition decode (n : option nat) : option instr := admit.
  Definition encode (i:instr) : option nat := admit.

  Theorem decode_encode : forall i, decode (encode i) = Some i.
  Proof. Admitted.
End EncDec.

Module EntryPoint.
  Definition data : Type := M.t (list Memory.address).

  Definition get C P E : Memory.address :=
    match M.find C E with
    | Some E' => nth P E' 0
    | None => 0
    end.

  Definition mem C (E : data) : bool := M.mem C E.

  Definition of_component C E : option (list Memory.address) :=
    M.find C E.

  Definition singleton C E : data := M.add C E (M.empty _).

  Definition filter (pc : list Component.id) (E : data) :=
    P.filter (fun C _ => existsb (fun C' => C =? C') pc) E.

  Lemma get_works_locally :
    forall E E' C P addrs,
      M.MapsTo C addrs E ->
      M.MapsTo C addrs E' ->
      get C P E = get C P E'.
  Proof.
    intros E E' C P addrs HEaddrs HE'addrs.
    unfold get.
    rewrite F.find_mapsto_iff in HEaddrs, HE'addrs.
    rewrite <- HEaddrs in HE'addrs.
    inversion HE'addrs as [HEeqE'].
    rewrite HEeqE'.
    reflexivity.
  Qed.
End EntryPoint.

Definition call_is_public_and_exists
           (Is : Program.interface)
           (C : Component.id) (P : Procedure.id) :=
  forall CI,
    find (fun C' => C =? Component.name C') Is = Some CI ->
    C < Component.export CI.

Definition call_is_in_imports
           (Is : Program.interface)
           (C C': Component.id) (P : Procedure.id) :=
  forall CI,
    find (fun C' => C =? Component.name C') Is = Some CI ->
    In (C',P) (Component.import CI).

Definition executing i C mem pc :=
  EncDec.decode (Memory.get mem C pc) = Some i.

End AbstractMachine.
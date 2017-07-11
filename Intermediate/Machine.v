Require Import Common.Definitions.
Require Import Common.Util.
Require Export Common.Values.
Require Export Common.Linking.

Module Intermediate.

Inductive register : Type :=
  R_ONE | R_COM | R_AUX1 | R_AUX2 | R_RA | R_SP.

Definition label := nat.

Inductive imvalue : Type :=
| IInt : nat -> imvalue
| IPtr : Pointer.t -> imvalue.

Definition imm_to_val (im : imvalue) : value :=
  match im with
  | IInt n => Int n
  | IPtr p => Ptr p
  end.

Inductive instr :=
| Nop : instr
| Label : label -> instr
(* register operations *)
| Const : imvalue -> register -> instr
| Mov : register -> register -> instr
| BinOp : binop -> register -> register -> register -> instr
(* memory operations *)
| Load : register -> register -> instr
| Store : register -> register -> instr
| Alloc : register -> register -> instr
(* conditional and unconditional jumps *)
| Bnz : register -> label -> instr
| Jump : register -> instr
| Jal : label -> instr
(* components interaction *)
| Call : Component.id -> Procedure.id -> instr
| Return : instr
(* termination *)
| Halt : instr.

Module Register.
  Definition t : Type := list value.

  Definition to_nat (r : register) : nat :=
    match r with
    | R_ONE  => 1
    | R_COM  => 2
    | R_AUX1 => 3
    | R_AUX2 => 4
    | R_RA   => 5
    | R_SP   => 6
    end.

  Definition init := repeat Undef 7.

  Definition get (r : register) (regs : t) : value :=
    match nth_error regs (to_nat r) with
    | Some val => val
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => Undef
    end.

  Definition set (r : register) (val : value) (regs : t) : t :=
    Util.Lists.update regs (to_nat r) val.

  Definition invalidate (regs : t) : t :=
    [Undef; Undef; get R_COM regs; Undef; Undef; get R_RA regs; Undef].

  Lemma init_registers_wf:
    forall r, exists val, get r init = val.
  Proof.
    intros r. unfold get.
    exists Undef. destruct r; auto.
  Qed.
End Register.

Module EntryPoint.
  Definition t := NMap.t (NMap.t Block.id).

  Definition get C P E : option Block.id :=
    match NMap.find C E with
    | Some addrs => NMap.find P addrs
    | None => None
    end.

  Lemma get_on_compatible_entrypoints :
    forall E E' C P addrs,
      NMap.MapsTo C addrs E ->
      NMap.MapsTo C addrs E' ->
      get C P E = get C P E'.
  Proof.
    intros E E' C P addrs HEaddrs HE'addrs.
    unfold get.
    rewrite NMapFacts.find_mapsto_iff in HEaddrs, HE'addrs.
    rewrite <- HEaddrs in HE'addrs.
    inversion HE'addrs as [HEeqE'].
    rewrite HEeqE'.
    reflexivity.
  Qed.

  Definition mergeable (e1 e2 : t) : Prop := NMapExtra.Disjoint e1 e2.
  
  Definition merge (e1 e2 : t) (mergeable_prf : mergeable e1 e2) : t :=
    NMapExtra.update e1 e2.
End EntryPoint.

(* programs *)

Definition code := list instr.

Record program := {
  prog_interface : Program.interface;
  prog_procedures : NMap.t (NMap.t code);
  prog_buffers : NMap.t (list (Block.id * nat));

  (* interface soundness *)
  prog_interface_soundness:
    sound_interface prog_interface;

  (* procedure soundness: TODO *)

  (* buffers soundness w.r.t. the interface *)
  prog_buffers_soundness:
    forall C, NMap.In C prog_buffers <-> NMap.In C prog_interface
}.

Definition closed_program (p : program) :=
  closed_interface (prog_interface p).

End Intermediate.
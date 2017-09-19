
(* Decribe machine (not state, that's in CS, just memory, values, etc.) *)

Require Import TargetMP.Monitor.

(* TODO: nat or Z? *)
Definition word := nat.

(* TODO: what to put in common? *)
(* TODO: why not Set over Type? *)
Inductive reg_id : Type :=
  R_ONE | R_COM | R_AUX1 | R_AUX2 | R_RA | R_SP.

Axiom binop : Type.
Axiom binop_intertprep : binop -> nat -> nat -> nat.

Inductive instr :=
| Nop : instr
(* register operations *)
| Const : word -> reg_id -> instr
| Mov : reg_id -> reg_id -> instr
| BinOp : binop -> reg_id -> reg_id -> reg_id -> instr
(* memory operations *)
| Load : reg_id -> reg_id -> instr
| Store : reg_id -> reg_id -> instr
| Alloc : reg_id -> reg_id -> instr
(* conditional and unconditional jumps *)
| Bnz : reg_id -> word -> instr
| Jump : reg_id -> instr
| Jal : word -> instr
(* termination *)
| Halt : instr.

(* At first, let's forget about encoding. *)
Axiom encode : instr -> nat.
Axiom decode : nat -> option instr.
(* TODO: equivalence axioms *)
Axiom encode_decode : forall i, decode (encode i) = Some i.
(* Axiom decode_encode : forall n i, decode n = Some i -> encode i = n. *)



(* TODO: is it the right representation? *)
Definition memory : Type := word -> (word * memtag).

(* TODO: map? no, see Intermediate.v; ask why *)
(* TODO: anyway, no Undef here! *)
Definition registers : Type := reg_id -> (word * regtag).

Definition pc : Type := word * pctag.

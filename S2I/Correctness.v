Require Import Common.Definitions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Source.Language.
Require Source.CS.
Require Import Intermediate.Machine.
Require Intermediate.CS.
Require Import S2I.Compiler.

(*
Taking inspiration from DSSS17 Leroy's lectures:
https://github.com/DeepSpec/dsss17/blob/master/compiler/Compiler.v

We want to prove a forward simulation from the source to the
intermediate level. In order to do that, we need to define a relation
between source states and intermediate states that we will use to
prove the main argument: starting from related states s1 (source) and
s2 (intermediate), if s1 takes a step to s1', then s2 can take zero or
more steps ending in a state s2' which is related to s1'.

        (s1)           related_states           (s2)
     Source.state ----------------------- Intermediate.state
                  |                     |
                  |                     | *
                  |                     |
       (s1')      v                     v       (s2')
    Source.state' ----------------------- Intermediate.state'
                       related_states

With the above simulation diagram, we have to take into account the
infinite stuttering problem: s1 takes infinitely many silent steps, whereas
s2 stays still forever (the source program diverges, but the
intermediate one doesn't). In all those cases in which s2 takes zero
steps, we have to invent a strictly decreasing measure on terms.

When does infinite stuttering occur in our case? We need to look at all
the source steps which do not correspond to the execution of a machine instruction:
- KS_Binop1: (C, s, mem, k, E_binop op e1 e2) -> (C, s, mem, Kbinop1 op e2 k, e1)
- KS_Seq1: (C, s, mem, k, E_seq e1 e2) -> (C, s, mem, Kseq e2 k, e1)
- KS_If: (C, s, mem, k, E_if e1 e2 e3) -> (C, s, mem, Kif e2 e3 k, e1)
- KS_Alloc1: (C, s, mem, k, E_alloc e) -> (C, s, mem, Kalloc k, e)
- KS_Deref1: (C, s, mem, k, E_deref e) -> (C, s, mem, Kderef k, e)
- KS_Assign1: (C, s, mem, k, E_assign e1 e2) -> (C, s, mem, Kassign1 e1 k, e2)
- KS_Call1: (C, s, mem, k, E_call C' P e) -> (C, s, mem, Kcall C' P k, e)

TODO find a measure for those cases

To relate source states with intermediate states, we need to define:
1. how a source expression is related to an instruction sequence
   (see codeseq_at in DSSS17)
2. how a source continuation is related to the remaining instructions
   (see compile_cont in DSSS17)

TODO define these two relations

Invariants of our compiled code:
- at the end of a sequence of compiled instructions, the register RCOM
  contains the evaluation result of the compiled expression
- at the end of a sequence of compiled instructions, the stack pointer
  is the same as the one with which the sequence started (basically, we
  handle the stack correctly, each PUSH has an associated POP)
- the register R_ONE always contains the value 1 (whenever we invalidate
  it during calls/returns, we have to restore it)
- the register R_AUX2 contains the origin of the call (1 if external, 0 otherwise)

At some point we will have to show that we allocated enough space for
the current stack frame (i.e. temporary values).

TODO how do we prove this fact?

Finally, we need to prove that initial states are related, and that final states
are quasi-related (we can take zero or more steps to reach an halt instruction).

TODO define and prove these lemmas

Once we have the above things, we can package them in forward_simulation object
defined by CompCert. Determinacy and receptiveness will then allow us to turn the
forward simulation into a backward one.

TODO prove determinacy and receptiveness
*)

Module S.
  Import Source.CS.
  Module CS := CS.
End S.

Module I.
  Import Intermediate.CS.
  Module CS := CS.
End I.

Section Correctness.

Variable p: Source.program.
Variable tp: Intermediate.program.

Hypothesis wellformed_input:
  Source.well_formed_program p.

Hypothesis successful_compilation:
  compile_program p = Some tp.

Theorem well_formedness_preservation:
  Intermediate.well_formed_program tp.
Proof.
Admitted.

Theorem I_simulates_S:
  forward_simulation (S.CS.sem p) (I.CS.sem tp).
Proof.
Admitted.

Corollary correct_compilation:
  backward_simulation (S.CS.sem p) (I.CS.sem tp).
Proof.
  apply forward_to_backward_simulation.
  - apply I_simulates_S.
  - apply S.CS.receptiveness.
  - apply I.CS.determinacy.
Qed.
End Correctness.

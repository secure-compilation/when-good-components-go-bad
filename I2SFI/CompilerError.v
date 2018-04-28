Require Import Coq.NArith.BinNat.
Require Import Common.CoqMaps.
Require Import AbstractMachine.

Inductive CompilerError : Type :=
| NoInfo : CompilerError
| DuplicatedLabels :
    (BinNatMap.t (BinNatMap.t AbstractMachine.lcode)) -> CompilerError
| ExportedProcsLabelsC :
    N ->
    (BinNatMap.t (BinNatMap.t  AbstractMachine.label)) ->
    CompilerError
| ExportedProcsLabelsP :
    N -> N ->
    (BinNatMap.t (BinNatMap.t AbstractMachine.label)) ->
    CompilerError
| NArg : N -> CompilerError
| ProcNotImported : N -> N -> list (N*N) -> CompilerError
| TwoNArg : N -> N -> CompilerError
.
Require Import I2SFI.CompilerError.
Require Import I2SFI.AbstractMachine.
Require Import Coq.Strings.String.
Require Import Common.CoqMaps.

Require Import Tests.CompTestUtil.
Require Import Tests.TargetSFI.SFITestUtil.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation QcNotation.
Open Scope qc_scope.
Open Scope string_scope.

Instance show_albl : Show AbstractMachine.label :=
  {|
    show := fun '(n1,n2) =>
               "("++ (show n1) ++ "," ++ (show n2) ++ ")"
  |}.

Instance show_ainstr : Show AbstractMachine.ainstr :=
  {| show :=
       fun i =>
         match i with
         | AbstractMachine.INop => "INop"
         | AbstractMachine.ILabel lbl => ("ILabel " ++ (show lbl))
         | AbstractMachine.IConst v r => "IConst " ++ (show v) ++ " " ++ (show r)
         | AbstractMachine.IMov r1 r2 => "IMov " ++ (show r1) ++ " " ++ (show r2)
         | AbstractMachine.IBinOp op r1 r2 r3 => "IBinop " ++ (show op)
                                          ++ " " ++ (show r1)
                                          ++ " " ++ (show r2)
                                          ++ " " ++ (show r3)
         | AbstractMachine.ILoad r1 r2 => "ILoad " ++ (show r1) ++ " " ++ (show r2)
         | AbstractMachine.IStore r1 r2 => "IStore " ++ (show r1) ++ " " ++ (show r2)
         | AbstractMachine.IBnz r l => "IBnz " ++ (show r) ++ " " ++ (show l)
         | AbstractMachine.IJump r => "IJump " ++ (show r)
         | AbstractMachine.IJal l => "IJal " ++ (show l)
         | AbstractMachine.IHalt => "IHalt"
         end
  |}.

Instance show_linstr : Show (option (list AbstractMachine.label) * AbstractMachine.ainstr) :=
  {|
    show :=
      fun '(ol,i) =>
        (show ol) ++ ":" ++ (show i)
  |}.


Definition show_lcode ( lcode : BinNatMap.t (BinNatMap.t AbstractMachine.lcode)) :=
  List.fold_left
    (fun acc1 '(cid, pmap) =>
       List.fold_left
         (fun acc2 '(pid, lst) =>
            List.fold_left
               (fun acc3 elt => acc3 ++ (show elt)  ++ newline)
               lst (acc2 ++ "pid=" ++ (show pid) ++ newline)%string
         ) (BinNatMap.elements pmap) (acc1 ++ "cid=" ++ (show cid) ++ newline)%string
    ) (BinNatMap.elements lcode) EmptyString.

Instance show_compiler_error : Show CompilerError :=
  {|
    show :=
      fun (err:CompilerError) =>
        match err with
        | NoInfo => EmptyString
        | DuplicatedLabels lcode => show_lcode lcode
        | ExportedProcsLabelsC p1 p2 => "ExportedProcsLabelsC "
                                                          ++ (show p1) ++ " "
                                                          ++ (show p2) ++ " "
        | ExportedProcsLabelsP p1 p2 p3 => "ExportedProcsLabelsP "
                                                          ++ (show p1) ++ " "
                                                          ++ (show p2) ++ " "
                                                          ++ (show_map p3) ++ " "
        | NArg p => show p
        | TwoNArg p1 p2 => "(" ++ (show p1) ++ "," ++ (show p2) ++ ")"
        | ProcNotImported cid pid lst =>
          "(" ++ (show cid) ++ "," ++ (show pid) ++ ")" ++ (show lst)
        end
  |}.

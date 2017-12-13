Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import Common.Maps.
Require Import Common.Definitions.
Require Import Common.Values.

Require Import Intermediate.Machine.

Require Import I2SFI.AbstractMachine.
Require Import I2SFI.CompEitherMonad.

Require Import TargetSFI.EitherMonad.
Require Import TargetSFI.SFITestUtil.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Definition newline := String "010" ""%string.

Definition show_map { A :Type} `{_ : Show A} (m : (PMap.t A)) : string :=
  List.fold_left
    (fun acc '(key,elt) =>
       acc ++ (show key) ++ ":" ++ newline
           ++ (show elt) ++ newline)
    (elementsm m)
    Coq.Strings.String.EmptyString.

Instance show_map_i  { A :Type} `{_ : Show A} : Show (PMap.t A) :=
  {| show := show_map |}.

Instance show_component_interface : Show Component.interface :=
  {|
    show := fun ci =>
              ("Export: ") 
                ++ (show (Component.export ci)) ++ newline
                ++ "Import:"
                ++ (show (Component.import ci)) ++ newline
  |}.


Instance show_ainstr : Show AbstractMachine.ainstr :=
  {| show :=
       fun i =>
         match i with
         | AbstractMachine.INop => "INop"
         | AbstractMachine.ILabel lbl => "ILabel " ++ (show lbl)
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

Definition show_lcode ( lcode : PMap.t (PMap.t AbstractMachine.lcode)) :=
  fold
    (fun cid (pmap:PMap.t AbstractMachine.lcode) (acc1:string) =>
       fold
         (fun pid (lst:AbstractMachine.lcode) acc2 =>
            List.fold_left
               (fun acc3 elt => acc3 ++ (show elt)  ++ newline)            
               lst (acc2 ++ "pid=" ++ (show pid) ++ newline)%string
         ) (elementsm pmap) (acc1 ++ "cid=" ++ (show cid) ++ newline)%string
    ) (elementsm lcode) EmptyString.

Instance show_compiler_error : Show CompilerError :=
  {|
    show :=
      fun (err:CompilerError) =>
        match err with
        | CompEitherMonad.NoInfo => EmptyString
        | CompEitherMonad.DuplicatedLabels lcode => show_lcode lcode
        | CompEitherMonad.ExportedProcsLabelsC _ _ => "ExportedProcsLabelsC TODO"
        | CompEitherMonad.ExportedProcsLabelsP _ _ _ => "ExportedProcsLabelsP TODO"
        | CompEitherMonad.PosArg p => show p
        | CompEitherMonad.TwoPosArg p1 p2 => "(" ++ (show p1) ++ "," ++ (show p2) ++ ")"
        end                                   
  |}.

Instance show_program_interface : Show Program.interface :=
  {| show := fun pi => show_map pi |}.

Instance show_ptr : Show Pointer.t :=
  {| show :=
       fun p => "( cid=" ++ (show (Pointer.component p))
                      ++ ",bid=" ++ (show (Pointer.block p))
                      ++ ",off=" ++ (show (Pointer.offset p))
                      ++ ")"
  |}.

Instance show_immv : Show imvalue :=
  {|
    show :=
      fun iv =>
        match iv with
        | IInt n => "IInt " ++ (show n)
        | IPtr p => "IPtr " ++ (show p)
        end
  |}.

Instance show_register : Show register :=
  {|
    show :=
      fun r =>
        match r with
        | R_ONE => "R_ONE"
        | R_COM => "R_COM"
        | R_AUX1 => "R_AUX1"
        | R_AUX2 => "R_AUX2"
        | R_RA => "R_RA"
        | R_SP => "R_SP"
        end
  |}.

Instance show_binop : Show Common.Values.binop :=
  {|
    show :=
      fun op =>
        match op with
        | Common.Values.Add => "+"
        | Common.Values.Minus => "-"
        | Common.Values.Mul => "*"
        | Common.Values.Eq => "="
        | Common.Values.Leq => "<="
        end
  |}.

Instance show_instr : Show Intermediate.Machine.instr :=
  {| show :=
       fun i =>
         match (i:Intermediate.Machine.instr) with
           | Intermediate.Machine.INop => "INop"
           | Intermediate.Machine.ILabel lbl => "ILabel " ++ (show lbl)
           | Intermediate.Machine.IConst v r => "IConst " ++ (show v) ++ " " ++ (show r)
           | Intermediate.Machine.IMov r1 r2 => "IMov " ++ (show r1) ++ " " ++ (show r2)
           | Intermediate.Machine.IBinOp op r1 r2 r3 => "IBinop " ++ (show op)
                                            ++ " " ++ (show r1)
                                            ++ " " ++ (show r2)
                                            ++ " " ++ (show r3)
           | Intermediate.Machine.ILoad r1 r2 => "ILoad " ++ (show r1) ++ " " ++ (show r2)
           | Intermediate.Machine.IStore r1 r2 => "IStore " ++ (show r1) ++ " " ++ (show r2)
           | Intermediate.Machine.IAlloc r1 r2 => "IAlloc " ++ (show r1) ++ " " ++ (show r2)
           | Intermediate.Machine.IBnz r l => "IBnz " ++ (show r) ++ " " ++ (show l)
           | Intermediate.Machine.IJump r => "IJump " ++ (show r)
           | Intermediate.Machine.IJal l => "IJal " ++ (show l) 
           | Intermediate.Machine.ICall cid pid => "ICall " ++ (show cid) ++ " " ++ (show pid)
           | Intermediate.Machine.IReturn => "IReturn"
           | Intermediate.Machine.IHalt => "IHalt"
         end
  |}.

Instance show_value : Show Common.Values.value :=
  {|
    show := fun val =>
              match val with
              | Int i => (show i)
              | Ptr p => (show p)
              | Undef => "Undef"
              end
  |}.

Instance show_buffers : Show (Block.id * (nat + list value)) :=
  {|
    show := fun p =>
              match p with
              | (bid, inl n) => (show bid) ++ "[" ++ (show n) ++"]"
              | (bid, inr lst) => (show bid) ++ ":" ++ (show lst)
              end             
  |}.

Instance show_intermediate_program : Show Intermediate.program :=
  {|
    show := fun ip =>
              ("Interface: ") ++ newline
                ++ (show (Intermediate.prog_interface ip))
                ++ ("Buffers: ") ++ newline
                ++ (show_map (Intermediate.prog_buffers ip))
                ++ ("Code: ") ++ newline
                ++ (show (Intermediate.prog_procedures ip))
                ++ ("Main: ") ++ newline
                ++ (show (Intermediate.prog_main ip))
                         
  |}.

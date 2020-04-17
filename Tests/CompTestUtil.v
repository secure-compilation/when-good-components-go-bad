Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import CompCert.Events.

Require Import Common.CoqMaps.
Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Either.

Require Import Intermediate.Machine.
Require Import Intermediate.CS.

Require Import I2SFI.AbstractMachine.

Require Import Tests.TestIntermediate.

Require Import extructures.ord.

From mathcomp Require Import ssreflect ssrfun ssrbool ssreflect.eqtype.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Open Scope string.

Definition newline := String "010" "".

Instance show_pos : Show positive :=
  {|
    show := fun p => show (Pos.to_nat p)
  |}.

Instance show_N : Show N :=
  {| show := fun n => show (N.to_nat n) |}.


Definition show_map { A :Type} `{_ : Show A} (m : (BinNatMap.t A)) : string :=
  List.fold_left
    (fun acc '(key,elt) =>
       acc ++ (show key) ++ ":" ++ newline
           ++ (show elt) ++ newline)
    (BinNatMap.elements m)
    Coq.Strings.String.EmptyString.


Instance show_map_i  { A :Type} `{_ : Show A} : Show (BinNatMap.t A) :=
  {| show := show_map |}.


Instance show_fset {A : ordType} `{_ : Show A} : Show ({fset A}) :=
  {|
    show :=
      fun s => show (val s)
  |}.

Instance show_component_interface : Show Component.interface :=
  {|
    show := fun ci =>
              ("Export: ")
                ++ (show (Component.export ci)) ++ newline
                ++ "Import:"
                ++ (show (Component.import ci)) ++ newline
  |}.

Definition show_nmap { A :Type} `{_ : Show A} (m : (NMap A)) : string :=
  List.fold_left
    (fun acc '(key,elt) =>
       acc ++ (show key) ++ ":" ++ newline
           ++ (show elt) ++ newline)
    (elementsm m)
    Coq.Strings.String.EmptyString.

Instance show_map_ni  { A :Type} `{_ : Show A} : Show (NMap A) :=
  {| show := show_nmap |}.


Instance show_program_interface : Show Program.interface :=
  {| show := fun pi => show_nmap pi |}.

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
        | R_ARG => "R_ARG"
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

Instance show_buff : Show ({fmap Block.id -> nat + list value}) :=
  {|
    show := fun buffers =>
              List.fold_left
                (fun acc '(bid,v) =>
                   acc ++
                   ( match v with
                   | inl n =>  (show bid) ++ "[" ++ (show n) ++"]"
                   | inr lst => (show bid) ++ ":" ++ (show lst)
                   end )
                )
                (elementsm buffers)
                Coq.Strings.String.EmptyString
  |}.



Instance show_intermediate_program : Show Intermediate.program :=
  {|
    show := fun ip =>
              ("Interface: ") ++ newline
                ++ (show (Intermediate.prog_interface ip))
                ++ ("Buffers: ") ++ newline
                ++ (show_nmap (Intermediate.prog_buffers ip))
                ++ ("Code: ") ++ newline
                ++ (show (Intermediate.prog_procedures ip))
                ++ ("Main: ") ++ newline
                ++ (show (Intermediate.prog_main ip))

  |}.


Definition list2fset {A:ordType} (l : list A) : {fset A} :=
  let fix app  l  :=
      match l with
      | nil => fset0
      | x::xs => fsetU (fset1 x) (app xs)
      end in
  app l.

Definition list2fmap {T:ordType} {S:Type} ( l : list (T*S) ) : {fmap T->S} :=
  let fix app l :=
      match l with
      | nil => emptym
      | (k,v)::xs => setm (app xs) k v
      end in
  app l.

Definition event_eqb (e1 e2 : CompCert.Events.event) : bool :=
  match (e1,e2) with
  | (ECall c1 p1 v1 c1', ECall c2 p2 v2 c2') => (Component.eqb c1 c2)
                                         && (Procedure.eqb p1 p2)
                                         && (Component.eqb c1' c2')
  | (ERet c1 v1 c1', ERet c2 v2 c2') => (Component.eqb c1 c2)
                                       && (Component.eqb c1' c2')
  | _ => false
  end.

Fixpoint sublist (l1 l2 : CompCert.Events.trace) : bool :=
    match l1 with
    | nil => true
    | x::xs1 =>
       match l2 with
       | nil => false
       | y::xs2 =>
         if event_eqb x y
         then (sublist xs1 xs2)
         else false
       end
    end.


From QuickChick Require Import Show.
From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From extructures Require Import fmap fset.
From CoqUtils Require Import word.

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.

Require Import Transitional.
(* Require Import I2MP.Encode.
Require Import I2MP.Linearize.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Exec.

Require Import MicroPolicies.Instance.
 *)
Require Import MicroPolicies.Utils.
Require Export Extraction.Definitions.
Require Import Intermediate.Machine.

Import DoNotation.

Require Import String.
Open Scope string.

Instance showInt : Show int :=
  {
  show i := match i with
            | Posz n => show n
            | Negz n => "−" ++ show n
            end
  }.

Instance showWord {k : nat} : Show (word k) :=
  {
  show m := show ( (int_of_word m)) (*fintype.nat_of_ord (eqtype.val m)*)
  }.

(* Instance showRegInt : Show (Types.reg mt) := *)
(*   { *)
(*   show r := show (int_of_word r) *)
(*   }. *)

Print value.

Instance showValue : Show value :=
 {
  show v := match v with
    | Int z => show z
    | Ptr p => "Pointer: (" ++ show p ++ ")"
    | Undef => "Undef"
  end
}.

Instance showTvalue : Show tvalue :=
 {
  show tv := show (val tv) (* TODO *)
}.

Instance showRegInter : Show (Register.t) :=
 {
 show r :=   foldl (fun acc '(n,v) =>
           acc ++ (show n) ++ " : "
               ++ (show v) ++ newline)
        "" r
 }.

Print Transitional.stackless.

Instance showStackless : Show (Transitional.stackless) :=
  {
  show s := let '(mem,regs,pc,Level n) := s in
   "Memory: NO" ++ newline ++ "Registers: " ++ (show regs) ++ newline ++ "pc: " ++ show pc ++ "; level: " ++ show n
  }.


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


Instance show_trans : Show Transitional.instr :=
  {| show :=
       fun i =>
         match (i:Transitional.instr) with
           | Transitional.TrNop => "TrNop"
           | Transitional.TrLabel (inl lbl) => "TrLabel " ++ (show lbl)
           | Transitional.TrLabel (inr lbl) => "TrLabel " ++ (show lbl)
           | Transitional.TrConst v r => "TrConst " ++ (show v) ++ " " ++ (show r)
           | Transitional.TrMov r1 r2 => "TrMov " ++ (show r1) ++ " " ++ (show r2)
           | Transitional.TrBinOp op r1 r2 r3 => "TrBinop " ++ (show op)
                                            ++ " " ++ (show r1)
                                            ++ " " ++ (show r2)
                                            ++ " " ++ (show r3)
           | Transitional.TrLoad r1 r2 => "TrLoad " ++ (show r1) ++ " " ++ (show r2)
           | Transitional.TrStore r1 r2 => "TrStore " ++ (show r1) ++ " " ++ (show r2)
           | Transitional.TrAlloc r1 r2 => "TrAlloc " ++ (show r1) ++ " " ++ (show r2)
           | Transitional.TrBnz r l => "TrBnz " ++ (show r) ++ " " ++ (show l)
           | Transitional.TrJump r => "TrJump " ++ (show r)
           | Transitional.TrJalNat l => "TrJalNat " ++ (show l)
           | Transitional.TrJalProc l => "TrJalProc " ++ (show l)
           | Transitional.TrHalt => "TrHalt"
         end
  |}.

Instance show_intermediate : Show Machine.instr :=
  {
    show i :=
      match i with
      | INop => "INop"
      | ILabel l => "ILabel " ++ (show l)
      | IConst im r => "IConst " ++ (show im) ++ " " ++ (show r)
      | IMov r1 r2 => "IMov " ++ (show r1) ++ " " ++ (show r2)
      | IBinOp b r1 r2 r3 => "IBinop " ++ (show b) ++ " " ++ (show r1) ++ " " ++ (show r2) ++ " " ++ (show r3)
      | ILoad  r1 r2 => "ILoad " ++ (show r1) ++ " " ++ (show r2)
      | IStore  r1 r2 => "IStore " ++ (show r1) ++ " " ++ (show r2)
      | IAlloc  r1 r2 => "IAlloc " ++ (show r1) ++ " " ++ (show r2)
      | IBnz r l => "IBnz " ++ (show r) ++ " " ++ (show l)
      | IJump r => "IJump " ++ (show r)
      | IJal l => "IJal " ++ (show l)
      | ICall c p => "ICall " ++ (show c) ++ " " ++ (show p)
      | IReturn => "IReturn"
      | IHalt => "IHalt"
      end
  }.

Definition show_nmap { A :Type} `{_ : Show A} (m : (NMap A)) : string :=
  List.fold_left
    (fun acc '(key,elt) =>
       acc ++ (show key) ++ ":" ++ newline
           ++ (show elt) ++ newline)
    (elementsm m)
    Coq.Strings.String.EmptyString.



Instance show_dummymemtag : Show LRC.mem_tag :=
 {
  show mt := ""
 }.

Instance show_seq  { A :Type} `{_ : Show A} : Show (list A) :=
{
  show l := let fix show_aux l := match l with 
    | [] => ""
    | i :: iss => show i ++ newline ++ show_aux iss
   end
  in show_aux l
}.

Instance show_code : Show Transitional.code :=
 {
  show c := show_nmap c
}.

Instance show_intermediate_code_aux : Show (NMap code) :=
 {
  show c := show_nmap c
}.

Instance show_intermediate_code : Show (NMap (NMap code)) :=
 {
  show c := show_nmap c
}.


Definition compile_and_show (p: Source.program) :=
  let str :=
      match compile_program p with
      | None => "Compilation failed"%string
      | Some inter_p =>
        let cde := (intermediate_to_transitional inter_p) in
        (* match execN fuel st with
        | (None, str) => str
        | (Some st, str) => str
        end*)
        show cde
      end in
  print_string_ocaml str.

(* Definition compile_and_run' (p: Intermediate.program) (fuel:nat) := *)
(*   let st := load (encode (linearize p)) in *)
(*     match execN fuel st with *)
(*     | None => print_error ocaml_int_1 *)
(*     | Some st' => fstate_to_unit (print_regs st' 6 fstate0) *)
(*     end *)
(* . *)

Require Import MicroPolicies.Merged MicroPolicies.Symbolic Int32.


Instance showRegisterTag : Show (Symbolic.tag_type LRC.lrc_tags Symbolic.R) :=
 {
  show rt := match rt with LRC.Ret n => "Ret " ++ (show n) | _ => "not Ret" end
}.


Instance showMemoryTag : Show (Symbolic.tag_type LRC.lrc_tags Symbolic.M) :=
 {
   show mt := (match LRC.vtag mt with | LRC.Ret n => ("Ret " ++ (show n)) | _ => "not ret" end)
               ++ " ; c=" ++ (show (LRC.color mt) ++
              (match (LRC.entry mt) with | None => " ; no entry" | Some e => " ; entry = " ++ (show e) end))
 }.


Definition tab := String (Ascii.ascii_of_pos 9) ""%string.

Definition register_of_nat (n : nat) : string :=
  match n with  
    | 0  => "R_ONE"
    | 1  => "R_COM"
    | 2  => "R_AUX1"
    | 3  => "R_AUX2"
    | 4  => "R_RA "
    | 5  => "R_SP "
    | 6  => "R_ARG"
    | 16 => "R_SC_RET"
    | 17 => "R_SC_ARG1"
    | 18 => "R_SC_ARG2"
    | 19 => "R_SC_ARG3"
    | _  => "NOT A REG"
  end.

Instance showRegister : Show (register) :=
  {
    show r := register_of_nat (Intermediate.Machine.Intermediate.Register.to_nat r)
  }.

Instance showSysreg : Show (Merged.sys_reg) :=
  {
    show r := register_of_nat (Merged.to_nat_bis (inr r))
  }.


Instance showRegSysreg : Show (register + Merged.sys_reg) :=
  {
    show r :=
      match r with
        | inl r => show r | inr r => show r
      end
  }.

Instance showRegisters : Show (@Merged.registers concrete_int_32_mt) :=
 {
 show r :=   foldl (fun acc '(n,v) =>
           acc ++ (register_of_nat ( n)) ++ " : " ++ tab 
               ++ (show (MicroPolicies.Types.vala v)) ++ " @ "
               ++ (show (MicroPolicies.Types.taga v)) ++ newline)
        "" (Maps.elementsm r)
 }.

Definition elementsm {A: Type} {k : nat} : {fmap (word k) -> A} -> list ((word k) * A).
Proof.
     exact (@FMap.fmval (word_ordType k) A _)
  ||
     idtac "ExStructures 0.1 legacy definition inactive";
     exact (@FMap.fmval (word_ordType k) A).
Defined.


Instance show_atom  { A B :Type} `{_ : Show A} {_ : Show B}: Show (Types.atom A B) :=
{
  show a := (show (Types.vala a)) ++ " @ " ++ (show (Types.taga a))
}.
(*
From deriving Require Import deriving.

Definition to_tag n := match n with 0 => LRC.Other | S m => LRC.Ret m end.
Definition of_tag t := match t with LRC.Other => 0 | LRC.Ret m => S m end.
Lemma cancel_tag : cancel of_tag to_tag. intro x ; destruct x ; simpl ; try reflexivity. Qed.

Definition value_tag_isOrder := CanOrdMixin cancel_tag. (* [derive orderMixin for (LRC.value_tag)]. *)

Notation atom := (Types.atom (Types.mword concrete_int_32_mt) (LRC.value_tag)).

Scheme atom_rect := Induction for (Types.atom (Types.mword concrete_int_32_mt) (LRC.value_tag)) Sort Type.

Definition at_indDef := Eval simpl in [indDef for atom_rect].
Canonical at_indType := IndType var var_indDef.
Definition at_eqMixin := Eval simpl in [derive eqMixin for var].
Canonical at_eqType := EqType var var_eqMixin.
Definition at_choiceMixin := [derive choiceMixin for var].
Canonical at_choiceType := Eval hnf in ChoiceType var var_choiceMixin.
Definition at_ordMixin := Eval simpl in [derive ordMixin for var].
Canonical at_ordType := OrdType var var_ordMixin.
Definition at_countMixin := [derive countMixin for var].
Canonical at_countType := Eval hnf in CountType var var_countMixin.
 *)
Notation mt := concrete_int_32_mt.
Notation ops := concrete_int_32_ops.


Instance show_mp : Show (Types.instr concrete_int_32_mt) :=
  {
    show i :=
      match i with
      | Types.Nop => "Nop"
      | Types.Const im r => "Const " ++ (show im) ++ " " ++ (show r)
      | Types.Mov r1 r2 => "Mov " ++ (show r1) ++ " " ++ (show r2)
      | Types.Binop b r1 r2 r3 => "Binop " ++ "todo : op" ++ " " ++ (show r1) ++ " " ++ (show r2) ++ " " ++ (show r3)
      | Types.Load  r1 r2 => "Load " ++ (show r1) ++ " " ++ (show r2)
      | Types.Store  r1 r2 => "Store " ++ (show r1) ++ " " ++ (show r2)
      | Types.Bnz r l => "Bnz " ++ (show r) ++ " " ++ (show l)
      | Types.Jump r => "Jump " ++ (show r)
      | Types.Jal l => "Jal " ++ (show l)
      | Types.Halt => "Halt"
      | _ => "error"
      end
  }.

Definition show_memory_word m := (match (Types.decode_instr m)  with
                                 | None =>  show m | Some i => show i end ).

Instance showMemory : Show (@Merged.memory mt) :=
  {
    
    show m := (* let m := mapm Types.vala m in
               let l := ((codomm m): list _) in
               foldl (fun acc m => acc ++ (show_memory_word m) ++ newline) "" l *)
      (* foldl (fun acc ad => acc ++ (odflt (show ad) (omap show (Types.decode_instr ad))) ++ newline) "" ((codomm m): list _) *)
    (* ( foldl (fun acc '(_,a) => acc ++ (show (Types.vala a)) ++ " | ") "" (elementsm m))*)
                 (* show   (map snd (elementsm m)) *)
                 (foldl (fun acc '(n,v) =>
           acc ++  (show n) ++ " : "
               ++ ((show_memory_word (Types.vala v))) ++ " @ "
               ++ (show (Types.taga v)) ++ newline)
        newline (elementsm m)) 
 }.

Instance showTrMemoryAux : Show (Memory.mem) :=
  {
    show m := show_nmap (Memory.content m)
  }.

Instance showTrMemory : Show (Memory.t) :=
  {
    show m := show_nmap m
  }.

Instance showState : Show (Merged.state) :=
  {
    show st :=
      let n := match (MicroPolicies.Types.taga (Merged.pc st)) with LRC.Level m => m end in
      "---------------------" ++ newline ++
        "Memory: " ++ newline ++ (show (Merged.mem st)) ++ newline ++
        "Registers: " ++ newline ++ (show (Merged.regs st )) ++ newline ++
        "pc: " ++ show (MicroPolicies.Types.vala (Merged.pc st)) ++
        "; level: " ++ show (ssrint.Posz n) ++ newline ++
        "---------------------" ++ newline
  }.


Instance showMergedInstr : Show (@Merged.instr concrete_int_32_mt) :=
  {
    show i := match i with              
  | MrNop     => "MrNop"
  | MrConst i r  => "MrConst " ++ (show i) ++ " " ++ (show r)
  | MrMov r1 r2   => "MrMov " ++ (show r1) ++ " " ++ (show r2)
  | MrBinop b r1 r2 r3 => "MrBinop " ++ (show b) ++ " " ++ (show r1) ++ " " ++ (show r2) ++ " " ++ (show r3)
  | MrLoad r1 r2  => "MrLoad " ++ (show r1) ++ " " ++ (show r2)
  | MrStore r1 r2 => "MrStore "++ (show r1) ++ " " ++ (show r2)
  | MrJump r   => "MrJump " ++ (show r)
  | MrBnz r l   => "MrBnz " ++ (show r) ++ " " ++ (show l)
  | MrJal l    => "MrJal " ++ (show l)
  | MrHalt    => "MrHalt "
  | MrLabel l  => "MrLabel " ++ (show l)
  end
  }.
  
Instance showMergedCode : Show (@Merged.code concrete_int_32_mt) :=
  {
    show c := "Merged code: " ++ (show (size c)) ++ " lines." ++ newline ++
   (let (_,s) := (foldl (fun (acc:(nat*string)) (p:(instr*LRC.mem_tag)) =>
                           let (n, a) := acc in let (i, t) := p in
                           (n+1, a ++ (show n) ++ " " ++ (show i) ++ " @ " ++ (show t) ++ newline)
                 ) (0,"") c) in s)
  }.

Definition printer {T : Type} (_:string) (v:T) : T := v.

Extract Constant printer => "(fun s v -> (List.fold_left (fun acc c -> print_char c; acc) () s); print_newline () ; v)". 

Fixpoint execN_and_show (n: nat) (cde: Merged.code) (st: state) : option Z + nat :=
  printer (show st)
  match n with
  | O => inr 3
  | S n' =>
    match @Merged.eval_step mt instr_rules cde st with
    | None => (inl (
             do! w <- (regs st (Intermediate.Machine.Intermediate.Register.to_nat R_COM));
             Some (Symbolic.convert (word.int_of_word (MicroPolicies.Types.vala w)))))
    | Some (st', _) => execN_and_show n' cde st'
    end
  end.

Fixpoint execN_pc (n: nat) (cde: Merged.code) (st: state) : option Z + nat :=
  printer (show (Types.vala (pc st)) ++ " ; ")
  match n with
  | O => inr 3
  | S n' =>
    match @Merged.eval_step mt instr_rules cde st with
    | None => (inl (
             do! w <- (@regs concrete_int_32_mt st (Intermediate.Machine.Intermediate.Register.to_nat R_COM));
             Some (Symbolic.convert (word.int_of_word (MicroPolicies.Types.vala w)))))
    | Some (st', _) => execN_pc n' cde st'
    end
  end.



(* execute transitional code and lists out the progam counters *)
Fixpoint execN_pc_trans (n: nat) (cde: Transitional.code) (st: stackless) : string :=
  let '(m,r,pc, Level pcl) := st in
  (show pc) ++ " @ Level" ++ (show pcl) ++" | R_RA : " ++ (show (Register.get R_RA r)) ++ " @ " ++(show (Register.get_tag R_RA r)) ++  " | R_SP : " ++ (show (r 5)) ++ "| R_AUX1 : " ++ (show (r 2)) ++ newline ++
            "---------------" ++ newline ++
            (show m) ++ newline ++ "---------------" ++ newline ++
  match n with
  | O => "out of fuel"
  | S n' =>
    match Transitional.eval_step cde st with
    | None =>
      let '(_, regs, _, _) := st in
      match val (Register.get R_COM regs) with
      | Int i => ("result : " ++ (show i))
      | _ =>  "error"
      end
    | Some (_, st') => execN_pc_trans n' cde st'
    end
  end.

(* execute interemdiary code and lists out the progam counters *)
Fixpoint execN_pc_inter (n: nat) (G: Intermediate.GlobalEnv.global_env) (st: Intermediate.CS.CS.state) : string :=
  let '(s,m,r,pc) := st in
  (show pc) ++ " | " ++
    (*"R_RA : " ++ (show (r 4)) ++ newline ++  " | R_SP : " ++ (show (r 5)) ++ newline ++
            "---------------" ++ newline ++
            (show s) ++ newline ++ "---------------" ++ newline ++*)
  match n with
  | O => "out of fuel"
  | S n' =>
    match Intermediate.CS.CS.eval_step G st with
    | None =>
      let '(_, _, regs, _) := st in
      match Intermediate.Machine.Intermediate.Register.get R_COM regs with
      | Int i => ("result : " ++ (show i))
      | _ => "error"
      end
    | Some (_, st') => execN_pc_inter n' G st'
    end
  end.

Definition run_inter_and_show_pc (n : nat) (p : Intermediate.program) : string :=
  let G := Intermediate.GlobalEnv.prepare_global_env p in
  let st := Intermediate.CS.CS.initial_machine_state p in
  execN_pc_inter n G st.

Definition run_trans_and_show_pc cd fuel p :=
    let mem  := Memory.prepare_procedures_initial_memory p in
    let regs := Register.init in
    match (find_plabel_in_code cd Component.main Procedure.main) with
    | Some pc =>
      execN_pc_trans fuel cd (mem,regs, pc, Level 0)
    | None => "no main"
end.


From CoqUtils Require Import hseq word.


Definition run_and_show_merged (cd:code) mem0 fuel nc :=
  let default_reg := {| MicroPolicies.Types.vala := (word_of_nat 0) ; MicroPolicies.Types.taga := (LRC.Other) |} in
  let reg0 := [fmap (0, default_reg) ;
               (1, default_reg) ;
               (2, default_reg) ;
               (3, default_reg) ;
               (4, {| MicroPolicies.Types.vala := (word_of_nat (1 + size cd)) ; MicroPolicies.Types.taga := (LRC.Other) |}) ;
               (5, default_reg) ;
               (6, default_reg) ;
               (16,default_reg) ;
               (17,default_reg) ;
               (18,default_reg) ;
               (19,default_reg) ] in
  let pctag := LRC.build_tpc 0 in
  let pc := {| MicroPolicies.Types.vala := (word_of_nat 0) ; MicroPolicies.Types.taga := pctag |} in
  let st := {|mem := mem0 ; regs := reg0 ; pc := pc ; comp_num := nc|} in
  printer (show cd)
  execN_and_show fuel cd st.

Definition compile_and_run_and_show_from_source_merged (mt : Types.machine_types) := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p =>
    printer (show (Intermediate.prog_procedures compiled_p))
    printer ( "intermediary pc : " ++ newline)
    printer (run_inter_and_show_pc fuel compiled_p)
    printer (show (intermediate_to_transitional compiled_p)) 
    printer ( "transitional pc : " ++ newline)
    printer (run_trans_and_show_pc (intermediate_to_transitional compiled_p) fuel compiled_p)
    match @run_and_show_merged (*concrete_int_32_mt*) (transitional_to_merged compiled_p (intermediate_to_transitional compiled_p)) (initial_memory compiled_p) fuel (1+ Nat.log2 (1 + (size (domm (Intermediate.prog_interface compiled_p))))) with
    | inl (Some n) => print_ocaml_int (z2int n)
    | inl None => print_error ocaml_int_1
    | inr n => print_error (nat2int n)
    end
| None => print_error ocaml_int_0
end.

Require Import Instance.

Definition word_of_reg {k : nat} r := (@Merged.word_of_nat k (Intermediate.Register.to_nat r)).

Instance showRegMap : Show ({fmap Types.reg concrete_int_32_mt ->
                             Types.atom (Types.mword concrete_int_32_mt)
                               (Symbolic.tag_type Symbolic.ttypes Symbolic.R)}) :=
  {
    show reg := (foldl (fun acc '(n,v) =>
                          acc ++ ((register_of_nat (Merged.nat_of_word n))) ++ " : "
                            ++ (show (MicroPolicies.Types.vala v)) ++ " @ "
                            ++ (show (MicroPolicies.Types.taga v)) ++ " | ")
                   "" (elementsm reg))
  }.

Instance showStateMP : Show (state) :=
  {
    show st :=
      let n := match (Types.taga (Symbolic.pc st)) with LRC.Level m => m end in
      "---------------------" ++ newline ++
        "Memory: " ++ (show (size (domm (Symbolic.mem st)))) ++ newline ++ 
        "Registers: " ++ newline ++ (show (@Symbolic.regs concrete_int_32_mt LRC.sym_lrc st )) ++ newline ++
        "pc: " ++ show (MicroPolicies.Types.vala (Symbolic.pc st)) ++
        "; level: " ++ show (ssrint.Posz n) ++ newline ++ "---------------------" ++
        newline
  }.


Fixpoint execN (n: nat) (st: state) : option Z + nat :=
  match n with
  | O => inr 3
  | S n' =>
    match stepf st with
    | None => (inl (
             do! w <- (Symbolic.regs st (word_of_reg R_COM));
             Some (Symbolic.convert (word.int_of_word (Types.vala w)))))
    | Some (st', _) =>
        execN n' st'
    end
  end.

Definition compile_and_run_mp (p: Source.program) (fuel:nat) :=
(*  printer ("executing merged :" ++ newline) *)
  match compile_program p with
  | None => print_error ocaml_int_0
  | Some inter_p =>
      let merged_p := (transitional_to_merged inter_p (intermediate_to_transitional inter_p)) in
      let nc := (1+ Nat.log2 (1 + (size (domm (Intermediate.prog_interface inter_p))))) in
      let st := load (merged_to_mp_backend inter_p merged_p) nc in
      match execN fuel st with
    | inl (Some n) => print_ocaml_int (z2int n)
    | inl None => print_error ocaml_int_1
    | inr n => print_error (nat2int n)
      end
  end
.

Fixpoint execN_and_show_mp (n: nat) (st: state) : option Z + nat :=
  printer ( show st )
   
  match n with
  | O => inr 3
  | S n' =>
    match stepf st with
    | None => (inl (
             do! w <- (Symbolic.regs st (word_of_reg R_COM));
             Some (Symbolic.convert (word.int_of_word (Types.vala w)))))
    | Some (st', _) =>
        execN_and_show_mp n' st'
    end
  end.

Definition compile_and_run_and_show_mp (p: Source.program) (fuel:nat) :=
(*  printer ("executing merged :" ++ newline) *)
  match compile_program p with
  | None => print_error ocaml_int_0
  | Some inter_p =>
      let merged_p := (transitional_to_merged inter_p (intermediate_to_transitional inter_p)) in
      let nc := (1+ Nat.log2 (1 + (size (domm (Intermediate.prog_interface inter_p))))) in
      let st := load (merged_to_mp_backend inter_p merged_p) nc in
     printer ("-------------" ++ newline ++ (show (merged_p)) ++ "-------------" ++ newline)
     printer ("-------------" ++ newline ++ (show (Symbolic.mem st)) ++ "-------------" ++ newline)
      match execN_and_show_mp fuel st with
    | inl (Some n) => print_ocaml_int (z2int n)
    | inl None => print_error ocaml_int_1
    | inr n => print_error (nat2int n)
      end
  end
.

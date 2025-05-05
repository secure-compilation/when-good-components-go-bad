Require Import Common.Definitions.

From CoqUtils Require Import hseq word.
From extructures Require Import fmap.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import Types.
Require Import Transitional.
Require Import MicroPolicies.Utils MicroPolicies.LRC MicroPolicies.Symbolic Intermediate.Machine.
Require Import CompCert.Events.


Require Import Source.Language S2I.Compiler.
Require Export Extraction.Definitions.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DoNotation.

Export Symbolic.

Section WithClasses.

Notation sp := sym_lrc.
  
Context {mt : machine_types} {ops : machine_ops mt}.

(* system call registers *)
Inductive sys_reg : Set :=
  R_SC_RET : sys_reg
| R_SC_ARG1 : sys_reg
| R_SC_ARG2 : sys_reg
| R_SC_ARG3 : sys_reg.


Variant instr :=
| MrNop : instr
| MrLabel : label -> instr
| MrConst : imm mt -> register -> instr
| MrMov : (register + sys_reg)  -> (register + sys_reg) -> instr
| MrBinop : binop -> register -> register -> register -> instr
| MrLoad : register -> register -> instr
| MrStore : register -> register -> instr
| MrJump : register -> instr
| MrBnz : register -> label -> instr
| MrJal : label -> instr
| MrHalt : instr.


Definition nat_of_word {k : nat} (w : (word k)) : nat := (ssrint.absz (word.int_of_word w)).
Definition word_of_nat {k : nat} (n : nat) : (word k) := (word.as_word (ssrint.Posz n)).

Local Notation tag_type := (Symbolic.tag_type lrc_tags).

Local Notation word := (mword mt).
Let atom := (Types.atom word).

Definition memory := {fmap word -> atom (tag_type Symbolic.M)}.
Definition registers := {fmap nat -> (atom (tag_type Symbolic.R))}%type.

Notation to_nat := Intermediate.Machine.Intermediate.Register.to_nat.
Definition from_nat (n : nat) : register :=
  match n with
    | 0 => R_ONE
    | 1 => R_COM
    | 2 => R_AUX1
    | 3 => R_AUX2
    | 4 => R_RA
    | 5 => R_SP
    | _ => R_ARG
  end.

Definition to_nat_bis (r : register + sys_reg) : nat :=
    match r with
    | inl r => to_nat r
    | inr r =>
        match r with
          R_SC_RET => 16
        | R_SC_ARG1 => 17
        | R_SC_ARG2 => 18
        | R_SC_ARG3 => 19
        end
    end.

Definition from_nat_bis (n : nat) : register + sys_reg :=
    match n with
    | 16 => inr R_SC_RET
    | 17 => inr R_SC_ARG1
    | 18 => inr R_SC_ARG2
    | 19 => inr R_SC_ARG3
    | _ => inl (from_nat n)
end.

Notation pc_type := (atom (tag_type Symbolic.P)).

Definition code := (seq (instr * mem_tag)).

Definition binop_of_binop (b : binop) : Types.binop :=
  match b with
  | Add => ADD
  | Minus => SUB
  | Mul => MUL
  | Eq => EQ
  | Leq => LEQ
  end.

Definition alloc_label := 2 ^ 14.

(*** Tagged -> Merged ***)

Fixpoint fold_left_map {FROM ACC TO: Type} (f : ACC -> FROM -> TO * ACC) (init : ACC) (l : list FROM) : list TO :=
  match l with
  | nil => nil
  | cons e ll => let (val,acc) := (f init e) in val :: (fold_left_map f acc ll)
end.

Fixpoint fold_left_map_bis {FROM ACC TO: Type} (f : ACC -> FROM -> TO * ACC) (init : ACC) (l : list FROM) : (list TO) * ACC :=
  match l with
  | nil => (nil, init)
  | cons e ll => let (val,acc) := (f init e) in let (res, a) := (fold_left_map_bis f acc ll) in (val :: res, a)
end.

(* gives you the beginning point of each buffers in memory *)
Definition memory_lengths (buf : NMap {fmap Block.id -> nat + seq value}):  NMap (NMap nat) :=
  let l := Maps.elementsm (mapm Maps.elementsm buf) in (* turns fmaps into lists *)
  let f := (fun acc => fold_left_map_bis (fun acc' (a : nat * (nat + seq value)) =>
                                     match (snd a) with
                                      | inl n => ((fst a, acc'), n + acc')
                                      | inr s => ((fst a, acc'), (size s) + acc') end ) acc) in
  mkfmap (fold_left_map (fun acc s => let (flat,count) := f acc (snd s) in
                           ((fst s, mkfmap (flat)), count + acc) ) 0 l).


Definition encode_int (z : Z) : ssrint.int :=
  match z with
  | Z0 => ssrint.Posz 0
  | Z.pos n => ssrint.Posz (ssrnat.nat_of_pos n)
  | Z.neg n => ssrint.Negz (ssrnat.nat_of_pos n)
  end.

Definition convert_value (memory_size : NMap (NMap nat)) (iv : imvalue) : imm mt :=
  match iv with
  | IInt z => word.as_word (encode_int z)
  | IPtr p => word_of_nat
      (Option.default (0)
         (do! map <- (memory_size (Pointer.component p));
          do! s <- (map :NMap nat) (Pointer.block p);
          Some (Z.to_nat (Z.add (Z.of_nat s) (Pointer.offset p)))))
  end.


Definition instr_translation (make_label : proc_label -> nat) (update_label : nat -> nat) (memory_size : NMap (NMap nat)) (i : Transitional.instr) : (seq instr) :=
  match i with
    | TrNop => MrNop :: nil
    | TrLabel (inl l) => MrLabel (update_label l) :: nil
    | TrLabel (inr pl) =>  (MrLabel (make_label pl)) :: nil
    | TrConst iv reg => MrConst (convert_value memory_size iv) reg :: nil
    | TrMov r1 r2 => MrMov (inl r1) (inl r2) :: nil
    | TrBinOp b r1 r2 r3 => MrBinop b r1 r2 r3 :: nil
    | TrLoad r1 r2 => MrLoad r1 r2 :: nil
    | TrStore r1 r2 => MrStore r1 r2 :: nil
    | TrAlloc rptr rsize =>let l :=
                          [:: (MrMov (inl rsize) (inr R_SC_ARG1)) ;
                             (MrMov (inl R_RA) (inr R_SC_ARG3))  ;
                             (MrJal alloc_label)  ;
                             (MrMov (inr R_SC_ARG3) (inl R_RA))  ;
                             (MrMov (inr R_SC_RET) (inl rptr))] in l 
    | TrBnz r l => MrBnz r (update_label l) :: nil
    | TrJump r => MrJump r :: nil
    | TrJalNat l => MrJal (update_label l) :: nil
    | TrJalProc pl => MrJal (make_label pl) :: nil
    | TrHalt => MrHalt :: nil
  end.

Notation prog_buffers := (NMap {fmap Block.id -> nat + seq value}).

Definition transitional_to_merged (pb : prog_buffers) (cde : Transitional.code) : code :=
  let memory_size := memory_lengths (pb) in
  let max_seq := (fun l => foldl Init.Nat.max 0 (map (fun p => match (fst p) with | TrLabel (inl la) => la | _ => 0 end) l )) in
  let lmax := foldl Init.Nat.max 0 (codomm(mapm max_seq cde)) in
  let max_seq := (fun l => foldl Init.Nat.max 0 (map (fun p => match (fst p) with | TrLabel (inr (_,p)) => p | _ => 0 end) l )) in
  let pmax := foldl Init.Nat.max 0 (codomm(mapm max_seq cde)) in
  let cmax := foldl Init.Nat.max 0 (domm cde) in
  let make_label := (fun pl => lmax * (cmax + 1) + 1 + (fst pl)*pmax + (snd pl)) in
  let update_label := (fun c old => old + lmax * (c)) in
  let f := (fun  (itrt: Transitional.instr * mem_tag) (c: code) =>
    let (itr, t) := itrt in
    let il := map (fun i => (i,t)) (instr_translation make_label (update_label (color t)) memory_size itr) in app il c) in
  let c :=  flatten(map snd  (Maps.elementsm cde)) in
  foldr f nil c.

(*** Merged -> MP ***)

Notation instr_merged := instr.
Require Import MicroPolicies.Types.

Definition binop_trans (b : Values.binop) : binop :=
  match b with
    Add => ADD
  | Minus => SUB
  | Mul => MUL
  | Eq => EQ
  | Leq => LEQ
end.
    

Definition instr_merged_to_mp (i : instr_merged) (label_pos : nat -> nat) (pos : nat) : @Types.instr mt :=
  match i with
  | MrNop | MrLabel _ => Nop mt
  | MrConst i r => Const i (word_of_nat (to_nat r))
  | MrMov r1 r2 => Mov (word_of_nat (to_nat_bis r1)) (word_of_nat (to_nat_bis r2))
  | MrBinop b r1 r2 r3 => Binop (binop_trans b) (word_of_nat (to_nat r1)) (word_of_nat (to_nat r2)) (word_of_nat (to_nat r3))
  | MrLoad r1 r2 => Load (word_of_nat (to_nat r1)) (word_of_nat (to_nat r2))
  | MrStore r1 r2 => Store (word_of_nat (to_nat r1)) (word_of_nat (to_nat r2))
  | MrJump r => Jump (word_of_nat (to_nat r))
  | MrBnz r l => Bnz (word_of_nat (to_nat r)) (word_of_nat ((label_pos l) - pos))
  | MrJal l => Jal (word_of_nat (label_pos l))
  | MrHalt => Halt mt
  end.

Definition encode_instr_mp := @Types.encode_instr mt ops.

Definition encode_instr i lp pos := encode_instr_mp (instr_merged_to_mp i lp pos).

Definition encode_instr_atom x lp pos : matom := (encode_instr (fst x) lp pos)@(snd x).

Definition findopt {A : Type} (pred : A -> bool) l : option nat :=
  foldr (fun el acc => match acc with | None => if pred el then Some 0 else acc | Some n => Some (n+1)
                    end) None l.

Definition encode_code (cde : code) (pc0 : nat) : memory :=
  let cde := cde ++ [(MrHalt, MTag Other Component.main None true )] in
  let code_length := size cde in
  let offset := pc0 + code_length in
  let is_label := (fun a p => match (fst p) with | MrLabel l => a == l | _ => false end) in
  let lp := (fun l => match (findopt (is_label l) cde ) with
                   | Some (n) => pc0 + n
                   | _ => l end) in
  let f := (fun x acc => ((encode_instr_atom x lp (offset - 1 - (snd acc))) :: (fst acc), S (snd acc)) ) in
  Tmp.mapk (fun x => word_of_nat (x + pc0)) (fmap_of_seq (fst (foldr f ([], 0) cde))).

(*** Initialization/Compilation ***)

(* code adapted from I2MP/Linearize.v *)

Notation bufs := {fmap (nat * nat * nat) -> (value * mem_tag)}.

Definition linearize_buf (pb : prog_buffers) (c : Component.id) (b : Block.id) : seq (value * mem_tag) :=
  Option.default [::] (do! map <- getm (pb) c ;
                       do! block <- getm map b ;
                       Some match block with
                            | inl n => repeat (Undef, def_mem_tag c false) n
                            | inr l => [seq (x, def_mem_tag c false) | x <- l]
                            end).

Definition linearize_bufs (pb : prog_buffers) : bufs :=
  let bufs' : NMap (NMap (NMap (value * mem_tag))) :=
      mapim (fun c map => mapim (fun b _ => fmap_of_seq (linearize_buf pb c b)) map) pb
  in Tmp.mapk (fun c => match c with (x, (y, z)) => (x, y, z) end)
              (uncurrym (mapm (fun m : NMap (NMap (value * mem_tag)) => uncurrym m) bufs')).


Definition initial_memory (pb : prog_buffers) :=
  (* TODO: move default buffers to their respective compartments *)
  let bufs := linearize_bufs pb in
    let base_adress c b :=
     (*  length of code + 1 + number of triples (c',b',_) such that (c', b') that occur before (c, b) *)
      (*length (Linearize.procedures p) + 1 +*)
      length (domm (filterm (fun x _ => match x with (c', b', _) => (c' < c) || ((c' == c) && (b' < b)) end) bufs))
  in
  let concretize := (fun p => match p with
                              | (c, b, o) =>
                                (* TL TODO: I have add notation issues, hence intZmod.addz... *)
                                ssrint.intZmod.addz (encode_int o) (ssrint.Posz (base_adress c b))
                              end) in
  let f (x : nat * nat * nat) : mword mt :=
    match x with (c, b, o) => word.as_word (concretize (c, b, Z.of_nat o)) end in
  let encode_memval : ((value * mem_tag) -> (atom mem_tag)) := (fun x =>
  {| vala := match fst x with
             | Int z => word.as_word (encode_int z)
             | Ptr p => word.as_word (concretize p)
             | Undef =>  word.as_word (ssrint.Posz 0) (* Invariant: should not be present *)
             end ;
     taga := snd x |})
  in Tmp.mapk f (mapm (encode_memval) bufs).

Definition reg0 : {fmap reg mt -> (@ratom mt) } :=
  [fmap (word_of_nat 0, Atom (word_of_nat 0) Other)
      ; (word_of_nat 1, Atom (word_of_nat 0) Other)
      ; (word_of_nat 2, Atom (word_of_nat 0) Other)
      ; (word_of_nat 3, Atom (word_of_nat 0) Other)
      ; (word_of_nat 4, Atom (word_of_nat (2 ^ 15)) Other)
      ; (word_of_nat 5, Atom (word_of_nat 0) Other)
      ; (word_of_nat 6, Atom (word_of_nat 0) Other)
      ; (word_of_nat 7, Atom (word_of_nat 0) Other)
      ; (word_of_nat 16, Atom (word_of_nat 0) Other)
      ; (word_of_nat 17, Atom (word_of_nat 0) Other)
      ; (word_of_nat 18, Atom (word_of_nat 0) Other)
      ; (word_of_nat 19, Atom (word_of_nat 0) Other)].


(* return the memory along with the first pc *)
Definition merged_to_mp_backend (pb : prog_buffers) (cde : code) : memory * nat :=
  let m := (initial_memory pb) in
  let pc0 := size m in
  let c := (encode_code cde pc0) in
  (unionm c m, pc0).

(*
(* tag the part of memory that will serve for the code in mp*)
Definition encode_code_placeholder (cde : code) (pc0 : nat) : {fmap word_ordType (word_size mt) -> atom mem_tag} :=
  Tmp.mapk (fun x => word_of_nat (x + pc0)) (fmap_of_seq (map (fun '(_,t) => Atom (word_of_nat 0) t) cde)).
 *)


Definition initial_state cde (pb : prog_buffers) (pi : Program.interface) : (Symbolic.state lrc_tags [eqType of unit]) :=
  let nc := (1+ Nat.log2 (1 + (size (domm pi)))) in
  let mem0 := (initial_memory pb) in
  let pc0 := (size mem0) in
  let pctag := build_tpc 0 in
  {|mem := unionm (encode_code cde pc0) mem0 ; regs := reg0 ; pc := (word_of_nat pc0)@pctag ; internal := tt; comp_num := nc|}.

End WithClasses.


Section WithClasses'.

Context {mt : machine_types}.

Definition instr_rules (rcom_val : Z)
  (op : opcode)
  tpc
  ti
  (ts : hseq _ (inputs op))
  tni :=
  (* checks that we're not executing data *)
  do! _ <- if (is_code ti) then Some tt else None;
  (* checks that we're not reading/writing code *)
  do! _ <- match op, ts  with
          | STORE,   [hseq _; _; ts]
          | LOAD,    [hseq _; ts; _] => if (is_code ts) then None else Some tt
          | _, _ => Some tt
          end;
  (* otherwise, same micro-policy *)
  do! out <- LRC.instr_rules {| Symbolic.rcom_value := rcom_val|} op tpc ti ts tni;
  let 'Symbolic.OVec trpc' tr' := (fst out) in
  Some ({| trpc := trpc' ; tr := tr' |}, snd out).

Context  {ops : machine_ops mt} {sregs : syscall_regs mt}.



Definition transfer (iv : Symbolic.ivec lrc_tags) (evi : Symbolic.ev_inputs) : option (Symbolic.vovec lrc_tags (Symbolic.op iv) * option event) :=
  match iv with (* TL TODO: ask someone obout this dependent boilerplate *)
  | Symbolic.IVec vop tpc ti ts tni =>
    match vop, ts, ti, tni return option (Symbolic.vovec _ vop * option event) with
    | (OP op), ts, ti, tni =>
        do! out:((ovec _ op) * option event) <- instr_rules (Symbolic.rcom_value evi) tpc ti ts tni;
        let (ov, ev) := out in
        Some (Symbolic.OVec op (trpc ov) (tr ov), ev)
    (* Monitor stuff *)
    | SERVICE, [hseq], ti, None => Some (tt, None)
    |       _,      _,  _,    _ => None
    end
  end.



Definition sym_lrc_merged : Symbolic.params := {|
  Symbolic.ttypes := lrc_tags;
  Symbolic.transfer := transfer;
  Symbolic.internal_state := [eqType of unit]
 |}.



(*
Definition alloc_fun (st : @Symbolic.state mt sym_lrc_merged) : option (Symbolic.state sym_lrc_merged) :=
  do! ra_val <- Symbolic.regs st ra;
  let next_pc := (vala ra_val)@(taga (Symbolic.pc st)) in
  (* TL TODO: Is using return address to compute calling component safe? *)
  do! ra_atom <- Symbolic.mem st (vala ra_val);
  let current_c := (color (taga ra_atom)) in
  let prefix := (LRC.component_memory_prefix (ssrint.Posz (1 + current_c)) (Symbolic.comp_num st)) in
  let mask := (LRC.component_memory_prefix (ssrint.Posz ((2 ^ (Symbolic.comp_num st))-1)) (Symbolic.comp_num st)) in
  let prefix_filter := (fun mw => ((word.andw mw mask) == prefix) ) in (* keep only words starting with exactly prefix *)
  (* TL TODO: Rely on the fact that it set implem is a sorted list, kinda fishy *)
  let max_addr := List.last (filter prefix_filter (domm (Symbolic.mem st))) (prefix) in
  (* create the new bloc *)
  let atom : matom := (word.as_word (ssrint.Posz 0))@(def_mem_tag current_c false) in
  do! size <- Symbolic.regs st syscall_arg1;
  do! length <- match word.int_of_word (vala size) with
                | ssrint.Posz x => Some x
                | ssrint.Negz _ => None
                end;
  let bloc :=
      mkseq (fun n => ((word.addw max_addr (word.as_word (ssrint.Posz(n + 2)))), atom)) (* this + 2 is giving you one unallocated word between each block *)
            length in
  let mem' := unionm (Symbolic.mem st) (mkfmap bloc) in
  (* return *)
  do! addr <- (do! x <- List.head bloc;
                 Some (fst x));
  do! regs' <- updm (Symbolic.regs st) (syscall_ret) addr@Other;
  Some (Symbolic.State sym_lrc_merged mem' regs' next_pc tt (Symbolic.comp_num st)). *)


Definition table : (Symbolic.syscall_table lrc_tags [eqType of unit]) :=
  [fmap ((word_of_nat alloc_label), (@Symbolic.Syscall mt lrc_tags [eqType of unit] tt LRC.alloc_fun ) )].

(*
Definition alloc_addr : imm mt := shlw 1%w (as_word (ssrint.Posz 14)). (* 1 << 14 ; as to be an imm for Jal, so under 2^15 *)
Definition table_lrc : @Symbolic.syscall_table mt lrc_tags [eqType of unit] :=
  [fmap (swcast alloc_addr, {| Symbolic.entry_tag := tt ; Symbolic.sem := LRC.alloc_fun |})].
*)
End WithClasses'.

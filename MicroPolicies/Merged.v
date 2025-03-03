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


Section WithClasses.

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

Notation pc_type := (atom (tag_type Symbolic.P)).

Record state := State {
                    mem : memory;
                    regs : registers;
                    pc : pc_type;
                    comp_num : nat (* smallest n such that number of components < 2^n *)
}.

Notation state_ev := (state * option event)%type.

Inductive update :=
  | RegWrite : (register + sys_reg) -> word -> update
  | RegRead  : (register + sys_reg) -> update
  | MemWrite : word -> word -> update
  | MemRead : word -> update
.


Definition code := (seq (instr * mem_tag)).

Local Notation "x .+1" := (x + 1).

Definition executing (cde : code) (pc : mword mt) tg (i : instr) : Prop :=
 nth_error cde (nat_of_word pc) = Some (i,tg).


Definition outputs := Symbolic.outputs.
Definition inputs := outputs.

Record ovec (op : opcode) : Type := OVec {
  trpc : tag_type Symbolic.P;
  tr   : hseq (tag_type) (outputs op);
  }.

Record ivec (op : opcode) : Type := IVec {
  tpc : tag_type Symbolic.P;
  ti  : tag_type Symbolic.M;
  ts  : hseq tag_type (inputs op)
}.

Definition instr_rules (rcom_val : Z)
  (op : opcode)
  (tpc : tag_type Symbolic.P)
  (ti  : tag_type Symbolic.M)
  (ts : hseq (tag_type) (inputs op))
  (tni : option (tag_type Symbolic.M))
  : option ((ovec op) * (option event)) :=
  let current := match ti with {| color := c |} => c end in
  let level := match tpc with Level n => n end in
  match op, ts return option (ovec op * option event) with
    
  | NOP,     [hseq]            => do! _ <- check_belong current tni;
                                     Some (OVec tpc ([hseq] : hseq _ (outputs NOP)), None)

  | CONST,   [hseq td]         => do! _ <- check_belong current tni;
                                     Some (OVec tpc ([hseq Other] : hseq _ (outputs CONST)), None)

  | MOV,     [hseq ts; td]     => do! _ <- check_belong current tni;
                                     Some (OVec tpc ([hseq Other; ts] : hseq _ (outputs MOV)), None)

  | BINOP b, [hseq tx; ty; td] => do! _ <- check_belong current tni;
                                     Some (OVec tpc ([hseq tx; ty; Other] : hseq _ (outputs  (BINOP b))), None)

  | LOAD,    [hseq tp; ts; td] => do! _ <- check_belong current tni;
                                     if belong current (Some ts) then
                                       let (ts', td') := switch_val ts Other in
                                       Some (OVec tpc ([hseq tp; ts'; td'] : hseq _ (outputs LOAD )), None)
                                     else
                                       Some (OVec tpc ([hseq tp; ts; Other] : hseq _ (outputs LOAD )), None)

  | STORE,   [hseq tp; ts; td] => do! _ <- check_belong current tni;
                                 do! _ <- check_belong current (Some td);
                                     let (td', _) := switch_val td ts in
                                     Some (OVec tpc ([hseq tp; Other; td'] : hseq _ (outputs  STORE)), None)

  | BNZ,     [hseq tx]         => do! _ <- check_belong current tni;
                                     Some (OVec tpc ([hseq tx] : hseq _ (outputs BNZ)), None)

  | JUMP,    [hseq tp]         => if belong current tni then
                                   Some (OVec  tpc ([hseq tp] : hseq _ (outputs JUMP)), None)
                                 else
                                   (* TL TODO: should forbid return if level = 0 ?         *)
                                   (*          I think it is already enforced by invariant *)
                                   (*          (unique Ret n)                              *)
                                   let ev := do! c' <- get_tni_color tni;
                                               Some (ERet current (rcom_val) c') in
                                   do! _ <- check_ret level.-1 tp;
                                     Some (OVec  (build_tpc level.-1) ([hseq Other] : hseq _ (outputs JUMP)), ev)

  | JAL,     [hseq tra]    => if belong current tni then
                                   Some (OVec  tpc ([hseq tra] : hseq _ (outputs JAL)), None)
                                 else
                                   let ev := do! c' <- get_tni_color tni;
                                             do! p  <- get_proc_name tni;
                                                 Some (ECall current p (rcom_val) c') in
                                   do! _ <- check_entry current tni;
                                       Some (OVec  (build_tpc level.+1) ([hseq Ret level] : hseq _ (outputs JAL)), ev)

  | _,     _                   => None
  end.

Definition next_state (st : state)
  (op : opcode)
  (iv : ivec op)
  (* (op : instr)
  (tpc : tag_type Symbolic.P)
  (ti  : tag_type Symbolic.M)
  (ts : hseq (tag_type) (inputs op)) *)
  (tni : option (tag_type Symbolic.M)) (* tni is the tag of the potential new pointer *)
  (k : ((ovec op) * (option event)) -> option state_ev) : option state_ev :=
  do! i <-  (regs st 1);
  do! i <- Some (Symbolic.convert (word.int_of_word (vala i)));
  do! ov <- instr_rules i (tpc iv) (ti iv) (ts iv) tni; (* i is the content of RCOM register - used in ECall/ERet events *)
    k ov.


Definition next_state_do_update (st : state) (tk : Symbolic.tag_kind)
           (tag : tag_type tk)
           (updt : update) : option state := 
  match tk, tag with
  | Symbolic.R, t => match updt with
        | RegWrite r x =>  let regs':= setm (regs st) (to_nat_bis r) (x@t) in
                          Some (State (mem st) regs' (pc st) (comp_num st))
        | RegRead r => do! a <- regs st (to_nat_bis r);
                      let regs' := setm (regs st) (to_nat_bis r) (vala a)@t in
                      Some (State (mem st) regs' (pc st) (comp_num st))
        | _ => None
        end
  | Symbolic.M, t => match updt with
        | MemWrite w1 w2 => let mem':= setm (mem st) w1 w2@t in
                           Some (State mem' (regs st) (pc st) (comp_num st))
        | MemRead w => do! a <- mem st w;
                      let mem' := setm (mem st) w (vala a)@t in
                      Some (State mem' (regs st) (pc st) (comp_num st))
        | _ => None
        end
  | Symbolic.P, t => None
  end.

Fixpoint next_state_do_updates (st : state) (tks : seq Symbolic.tag_kind)
         (tags : hseq (tag_type) tks)
         (updts : seq update) : option state :=
  match tks, tags with
    | [:: ], _ => Some st
    | [:: tk & tks' ], tags =>
        do! updt <- ohead updts;
        do! st' <- next_state_do_update st (hshead tags) updt;
        next_state_do_updates st' (hsbehead tags) (behead updts)
  end.

(* pc' is the new, target pc *)
Definition next_state_updates_and_pc (cde : code) (st : state) 
  (op : opcode)
  (iv : ivec op)
  (updts : seq update)
  (pc' : word) : option state_ev :=
  let tni := match ((nth_error cde (nat_of_word pc'))) with | None => None | Some (_,t) => Some (t) end in
  let k :=
    (fun (ov_ev:((ovec op) * (option event))) => let (ov,ev) := ov_ev in
       do! st' <- next_state_do_updates st (tr ov) updts;
       Some (State (mem st') (regs st') pc'@(trpc ov) (comp_num st), ev)
    ) in
  next_state st iv tni k.

Definition next_state_updates (cde : code) (st : state) 
  (op : opcode)
  (iv : ivec op)
  (updts : seq update) : option state_ev :=
  next_state_updates_and_pc cde st iv updts (word_of_nat (nat_of_word (vala (pc st))).+1).

Fixpoint find_label_aux (cde : code) (l : label) (n : nat) : option nat :=
  match cde with
  | nil => None
  | cons (MrLabel l2, _) ccde => if (eqn l l2) then (Some n) else find_label_aux ccde l (n+1)
  | cons _ ccde => find_label_aux ccde l (n+1)
  end.

(* TODO : check for potential off-by-one error *)
(* find the word w of a pc pointing to the label l in cde *)
Definition find_label (cde : code) (l : label) : option nat :=
  find_label_aux cde l 0.

Definition binop_of_binop (b : binop) : Types.binop :=
  match b with
  | Add => ADD
  | Minus => SUB
  | Mul => MUL
  | Eq => EQ
  | Leq => LEQ
  end.

(* allows to split memory between components *)
Definition component_memory_prefix (c : nat) (nc : nat) :=
 @word.shlw (word_size mt) (word_of_nat (c)) (word_of_nat ((word_size mt) - nc)). (* left shift *)

Definition alloc_fun (cde : code) (st : state) : option state :=
  let prefix := (component_memory_prefix (nat_of_word ( vala (pc st))) (comp_num st)) in
  let mask := (component_memory_prefix ((2 ^ (comp_num st))-1) (comp_num st)) in
  let prefix_filter := (fun mw => ((word.andw mw mask) == prefix) ) in (* keep only words starting with exactly prefix *)
  do! current_instr <- nth_error cde (nat_of_word (vala (pc st)));
  let current_c := (color (snd current_instr)) in
  (* TL TODO: Rely on the fact that it set implem is a sorted list, kinda fishy *)
  let max_addr := last (prefix) (filter prefix_filter (domm (mem st))) in
  do! ra_val <- regs st (to_nat R_RA);
  let next_pc := (vala ra_val)@(taga (pc st)) in
  (* create the new bloc *)
  let atom : matom := (word.as_word (ssrint.Posz 0))@(def_mem_tag current_c) in
  do! size <- regs st (to_nat_bis (inr R_SC_ARG1));
  do! length <- match word.int_of_word (vala size) with
                | ssrint.Posz x => Some x
                | ssrint.Negz _ => None
                end;
  let bloc :=
      mkseq (fun n => ((word.addw max_addr (word.as_word (ssrint.Posz (n + 2)))), atom)) (* this + 2 is giving you one unallocated word between each block *)
            length in
  let mem' := unionm (mem st) (mkfmap bloc) in
  (* return *)
  do! addr <- (do! x <- hd_error bloc;
                 Some (fst x));
  let regs' := setm (regs st) (to_nat_bis (inr R_SC_RET)) addr@Other in
  Some (State mem' regs' next_pc (comp_num st)).


Definition alloc_label := 2 ^ 14.

Inductive step (cde : code) (st st' : state) (ev : option event) : Prop :=
| step_nop : forall mem reg pc tpc ti nc
    (ST   : st = State mem reg pc@tpc nc)
    (INST : executing cde pc ti MrNop),
    let mvec : ivec NOP := IVec tpc ti ([hseq] : hseq _ (inputs NOP)) in forall
    (NEXT : next_state_updates cde st mvec [:: ] = Some (st', ev)),    step cde st st' ev
| step_label : forall mem reg pc tpc ti l nc
    (ST   : st = State mem reg pc@tpc nc)
    (INST : executing cde pc ti (MrLabel l)),
    let mvec : ivec NOP := IVec tpc ti ([hseq] : hseq _ (inputs NOP)) in forall
    (NEXT : next_state_updates cde st mvec [:: ] = Some (st', ev)),    step cde st st' ev
| step_const : forall mem reg pc tpc ti n r old (told : tag_type Symbolic.R) nc
    (ST   : st = State mem reg pc@tpc nc)
    (INST : executing cde pc ti (MrConst n r))
    (OLD  : reg (to_nat r) = Some old@told),
    let mvec := IVec tpc ti ([hseq told] : hseq _ (inputs CONST)) in forall
    (NEXT : next_state_updates cde st mvec [:: RegWrite (inl r) (swcast n)] = Some (st', ev)),   step cde st st' ev
| step_mov : forall mem reg pc tpc ti r1 w1 t1 r2 old told nc
    (ST   : st = State mem reg pc@tpc nc)
    (INST : executing cde pc ti (MrMov r1 r2))
    (R1W  : reg (to_nat_bis r1) = Some w1@t1)
    (OLD  : reg (to_nat_bis r2) = Some old@told),
    let mvec := IVec tpc ti ([hseq t1; told] : hseq _ (inputs MOV)) in forall
    (NEXT : next_state_updates cde st mvec [:: RegRead r1 ; RegWrite r2 w1 ] = Some (st', ev)),   step cde st st' ev
| step_binop : forall mem reg pc tpc ti op r1 r2 r3 w1 w2 t1 t2 old told nc
    (ST   : st = State mem reg pc@tpc nc)
    (INST : executing cde pc ti (MrBinop op r1 r2 r3))
    (R1W  : reg (to_nat r1) = Some w1@t1)
    (R2W  : reg (to_nat r2) = Some w2@t2)
    (OLD  : reg (to_nat r3) = Some old@told),
    let mvec := IVec tpc ti ([hseq t1; t2; told] : hseq _ (inputs (BINOP (binop_of_binop op)))) in forall
    (NEXT : next_state_updates cde st mvec [:: RegRead (inl r1) ; RegRead (inl r2) ; RegWrite (inl r3) (binop_denote (binop_of_binop op) w1 w2) ] = Some (st', ev)),
      step cde st st' ev
| step_load : forall mem reg pc tpc ti r1 r2 w1 w2 t1 t2 old told nc
    (ST   : st = State mem reg pc@tpc nc)
    (INST : executing cde pc ti (MrLoad r1 r2))
    (R1W  : reg (to_nat r1) = Some w1@t1)
    (MEM1 : mem w1 = Some w2@t2)
    (OLD  : reg (to_nat r2) = Some old@told),
    let mvec := IVec tpc ti ([hseq t1; t2; told] : hseq _ (inputs LOAD)) in forall
    (NEXT : next_state_updates cde st mvec [:: RegRead (inl r1) ; MemRead w1 ; RegWrite (inl r2) w2 ] = Some (st', ev)),
    step cde st st' ev
| step_store : forall mem reg pc r1 r2 w1 w2 tpc ti t1 t2 old told nc
    (ST   : st = State mem reg pc@tpc nc)
    (INST : executing cde pc ti (MrStore r1 r2))
    (R1W  : reg (to_nat r1) = Some w1@t1)
    (R2W  : reg (to_nat r2) = Some w2@t2)
    (OLD  : mem w1 = Some old@told),
    let mvec := IVec tpc ti ([hseq t1; t2; told] : hseq _ (inputs STORE)) in forall
    (NEXT : next_state_updates cde st mvec [:: RegRead (inl r1) ; RegRead (inl r2) ; MemWrite w1 w2 ] = Some (st', ev)),
    step cde st st' ev
| step_jump : forall mem reg pc r w tpc ti t1 nc
    (ST   : st = State mem reg pc@tpc nc)
    (INST : executing cde pc ti (MrJump r))
    (RW   : reg (to_nat r) = Some w@t1),
    let mvec := IVec tpc ti ([hseq t1] : hseq _ (inputs JUMP)) in forall
    (NEXT : next_state_updates_and_pc cde st mvec [:: RegRead (inl r) ] w = Some (st', ev)),
    step cde st st' ev
| step_bnz : forall mem reg pc r n w tpc ti t1 nc
    (ST   : st = State mem reg pc@tpc nc)
    (INST : executing cde pc ti (MrBnz r n))
    (RW   : reg (to_nat r) = Some w@t1),
    let mvec := IVec tpc ti ([hseq t1] : hseq _ (inputs BNZ)) in
    let optpc' := (if w == (word_of_nat 0) then Some ((nat_of_word (pc)) + 1) else find_label cde n) in forall pc' (PC' : optpc' = Some pc')
    (NEXT : next_state_updates_and_pc cde st mvec [:: RegRead (inl r) ] (word_of_nat pc') = Some (st', ev)),
    step cde st st' ev
| step_jal : forall mem reg pc l tpc ti old told pc' nc
    (ST : st = State mem reg pc@tpc nc)
    (INST : executing cde pc ti (MrJal l))
    (OLD : reg (to_nat R_RA) = Some old@told)
    (NOT_ALLOC : l <> alloc_label),
    let mvec := IVec tpc ti ([hseq told] : hseq _ (inputs JAL)) in
    forall (PC' :  Some pc' = (find_label cde l))
    (NEXT : next_state_updates_and_pc cde st mvec [:: RegWrite (inl R_RA) (word_of_nat((nat_of_word pc).+1)) ] (word_of_nat pc') = Some (st', ev)),
    step cde st st' ev
| step_jal_alloc : forall mem reg pc  l tpc ti old told st_inter nc
    (ST : st = State mem reg pc@tpc nc)
    (INST : executing cde pc ti (MrJal l))
    (OLD : reg (to_nat R_RA) = Some old@told)
    (ALLOC : l = alloc_label),
    let mvec := IVec tpc ti ([hseq told] : hseq _ (inputs JAL)) in
    forall (NEXT : @next_state_do_update st Symbolic.R Other ( RegWrite (inl R_RA) (word_of_nat((nat_of_word pc).+1))) = Some st_inter)
      (*NEXT : next_state_updates_and_pc cde st mvec [:: RegWrite (inl R_RA) (word_of_nat((nat_of_word pc).+1)) ] pc' = Some (st_inter, ev)*)
    (ST' : (alloc_fun cde st_inter) = Some st') (EV : ev = None),
    step cde st st' ev
.


Definition eval_step (cde : code) (st : state) : option state_ev := 
  let 'State mem reg pc@pctag nc := st in
  match (nth_error cde (nat_of_word pc)) with
  | None =>None
  | Some (instr,ti) =>
    match instr with
    | MrNop | MrLabel _ =>
      let mvec := IVec pctag ti ([hseq] : hseq _ (inputs NOP)) in
      next_state_updates cde st mvec [:: ]
    | MrConst n r =>
      do! old <- reg (to_nat r);
      let: _@told := old in
      let ivec := IVec pctag ti ([hseq told] : hseq _ (inputs CONST)) in
      next_state_updates cde st ivec [:: RegWrite (inl r) (swcast n)]
    | MrMov r1 r2 =>
      do! a1 <- reg (to_nat_bis r1);
      let: w1@t1 := a1 in
      do! a2 <- (reg (to_nat_bis r2));
      let: _@told := a2 in
      let mvec := IVec pctag ti ([hseq t1;told] : hseq _ (inputs MOV)) in
      next_state_updates cde st mvec [:: RegRead r1 ; RegWrite r2 w1]
    | MrBinop op r1 r2 r3 =>
      do! a1 <- reg (to_nat r1);
      let: w1@t1 := a1 in
      do! a2 <- reg (to_nat r2);
      let: w2@t2 := a2 in
      do! a3 <- reg (to_nat r3);
      let: _@told := a3 in
      let mvec := IVec pctag ti ([hseq t1;t2;told] : hseq _ (inputs (BINOP (binop_of_binop op)))) in
      next_state_updates cde st mvec [:: RegRead (inl r1) ; RegRead (inl r2) ; RegWrite (inl r3) (binop_denote (binop_of_binop op) w1 w2)]
    | MrLoad r1 r2 =>
      do! a1 <- reg (to_nat r1);
      let: w1@t1 := a1 in
      do! amem <- mem w1;
      let: w2@t2 := amem in
      do! a2 <- reg (to_nat r2);
      let: _@told := a2 in
      let mvec := IVec pctag ti ([hseq t1;t2;told] : hseq _ (inputs LOAD)) in
      next_state_updates cde st mvec [:: RegRead (inl r1) ; MemRead w1 ; RegWrite (inl r2) w2]
    | MrStore r1 r2 =>
      do! a1 <- reg (to_nat r1);
      let: w1@t1 := a1 in
      do! amem <- mem w1;
      let: _@told := amem in
      do! a2 <- reg (to_nat r2);
      let: w2@t2 := a2 in
      let mvec := IVec pctag ti ([hseq t1;t2;told] : hseq _ (inputs STORE)) in
      next_state_updates cde st mvec [:: RegRead (inl r1) ; RegRead (inl r2) ; MemWrite w1 w2]
    | MrJump r =>
      do! a <- reg (to_nat r);
      let: w@t1 := a in
      let mvec := IVec pctag ti ([hseq t1] : hseq _ (inputs JUMP)) in
      next_state_updates_and_pc cde st mvec [:: RegRead (inl r)] w
    | MrBnz r n =>
      do! a <- reg (to_nat r);
      let: w@t1 := a in
      do! pc' <- (if w == (word_of_nat 0) then Some ((nat_of_word (pc)) + 1) else find_label cde n);
      let ivec := IVec pctag ti ([hseq t1] : hseq _ (inputs BNZ)) in
      next_state_updates_and_pc cde st ivec [:: RegRead (inl r)] (word_of_nat pc')
    | MrJal i =>
        do! oldtold <- reg (to_nat R_RA);
        let: _@told := oldtold in
        if (i == alloc_label) then
        do! st_inter <- (@next_state_do_update st Symbolic.R Other ( RegWrite (inl R_RA) (word_of_nat((nat_of_word pc).+1))));
        do! st' <- alloc_fun cde st_inter;
        Some (st', None)
      else
        let mvec := IVec pctag ti ([hseq told] : hseq _ (inputs JAL)) in
        match (find_label cde i) with
        | None => None
        | Some (pc') => next_state_updates_and_pc cde st mvec [:: RegWrite (inl R_RA) (word_of_nat((nat_of_word pc).+1))] (word_of_nat pc')
        end
    | MrHalt => None
    end
  end.


Theorem eval_step_complete:
  forall cd st st' ev, step cd st st' ev -> eval_step cd st = Some (st', ev).
Proof.
  intros. inversion H ;
  try (unfold executing in INST ) ;
  try (unfold eval_step ; rewrite ST ; rewrite INST ; rewrite <- ST ; unfold mvec in NEXT) ;
  try (rewrite R1W) ; simpl ; try (rewrite R2W) ; simpl ; try (rewrite RW ) ; simpl ;
  try (rewrite MEM1); simpl ; try (rewrite OLD) ; simpl ; try exact NEXT.
  + unfold optpc' in PC'. rewrite PC'. auto.
  + remember (l == alloc_label) as cond. induction cond ; try (rewrite <- PC' ; exact NEXT).
    unfold "==", nat_eqType, nat_eqMixin in Heqcond; simpl.
    inversion Heqcond as [eq]. destruct (@eqnP l alloc_label). destruct (NOT_ALLOC e). inversion eq.
  + rewrite ALLOC.  rewrite EV.
    remember {|mem := mem st; regs := setm (regs st) 4 (word_of_nat (nat_of_word pc0).+1)@Other;
     pc := pc st ; comp_num := comp_num st|} as st_alt. cut (st_alt = st_inter).
    ++ intro eq. rewrite <- eq in ST'. rewrite Heqst_alt in ST'. rewrite ST'. auto.
    ++ unfold next_state_do_update in NEXT. unfold to_nat_bis in NEXT. unfold to_nat in NEXT.
       inversion NEXT. exact Heqst_alt.
Qed.


(* those tactics help when STEP_EQ contains something of the form  "do! _ <- regs0 (f s);" *)

Ltac resolve_register regs0 STEP_EQ s f :=
  let rval  := fresh in
  remember (regs0 (f s)) as rval ; destruct rval ; simpl in STEP_EQ. 
  
Ltac resolve_register_deep regs0 STEP_EQ s f :=
  let save  := fresh in 
  let Heqsave := fresh in 
  let rval  := fresh in 
  let Heqrval := fresh in 
       remember (regs0 (f s)) as save eqn:Heqsave ;
       unfold Option.bind, oapp, getm in STEP_EQ ;
       remember (getm_def regs0 (f s)) as rval eqn:Heqrval ;
       cut (rval = save) ; try (rewrite Heqsave ; rewrite Heqrval ; reflexivity) ;
       unfold getm_def in STEP_EQ ; unfold getm_def in Heqrval ;
       simpl in Heqrval ; simpl in STEP_EQ ; rewrite <- Heqrval in STEP_EQ ; destruct rval.
      (* +++ destruct a. intro tageq. rewrite <- tageq in Heqsave. *)


Ltac resolve_memory_deep regs0 STEP_EQ s :=
  let save  := fresh in 
  let Heqsave := fresh in 
  let rval  := fresh in 
  let Heqrval := fresh in 
       remember (regs0 s) as save eqn:Heqsave ;
       unfold Option.bind, oapp, getm in STEP_EQ ;
       remember (getm_def regs0 s) as rval eqn:Heqrval ;
       cut (rval = save) ; try (rewrite Heqsave ; rewrite Heqrval ; reflexivity) ;
       unfold getm_def in STEP_EQ ; unfold getm_def in Heqrval ;
       simpl in Heqrval ; simpl in STEP_EQ ; rewrite <- Heqrval in STEP_EQ ; destruct rval.

Lemma eq_op_to_eq : forall (x y : nat), (x = y) <-> (true = (x == y)).
Proof.
  intro x.
  induction x ; split ; intro eq ; try ( induction y ; try reflexivity ; inversion eq ).
  + unfold "==", nat_eqType, nat_eqMixin. simpl.
    unfold "==", nat_eqType, nat_eqMixin in IHx.
    remember (IHx y) as a. destruct a as [l r]. simpl in l. destruct Heqa. rewrite H0 in l.
    apply l. reflexivity.
  + cut (x=y).
    ++ intro. auto.
    ++ apply IHx. auto.
Qed.

Theorem eval_step_sound:
  forall cd st st' ev
    (STEP_EQ : eval_step cd st = Some (st', ev)), step cd st st' ev.
  intros. unfold eval_step in STEP_EQ.
  induction st.  induction pc0 as [pcv pctag].
  remember ({| mem := mem0; regs := regs0; pc := pcv@pctag |}) as st.
  remember (nth_error cd (nat_of_word pcv)) as nth.
  destruct nth as [iti|]. destruct iti as [i ti].
  induction i.
  + apply (step_nop Heqst (esym Heqnth) STEP_EQ). 
  + apply (step_label Heqst (esym Heqnth) STEP_EQ). 
  + remember (regs0 (to_nat r)) as rval. destruct rval ; simpl in STEP_EQ.
    ++ destruct a as [old told].
       apply (step_const Heqst (esym Heqnth) (esym Heqrval) STEP_EQ).
    ++ inversion STEP_EQ.
  + resolve_register regs0 STEP_EQ s to_nat_bis.
    ++ destruct a as [old told]. resolve_register_deep regs0 STEP_EQ s0 to_nat_bis.
       +++ destruct a as [old0 told0]. intro tageq. rewrite <- tageq in H0.
           apply (step_mov Heqst (esym Heqnth) (esym HeqH) (esym H0) STEP_EQ). 
       +++ inversion STEP_EQ. 
    ++ inversion STEP_EQ.
  + resolve_register regs0 STEP_EQ r to_nat.
    ++ destruct a as [w1 t1]. resolve_register_deep regs0 STEP_EQ r0 to_nat.
       +++ destruct a as [old0 told0]. intro tageq. rewrite <- tageq in H0.
           resolve_register_deep regs0 STEP_EQ r1 to_nat.
           ++++ destruct a as [old1 told1]. intro tageq1. rewrite <- tageq1 in H3.
                apply (step_binop Heqst (esym Heqnth) (esym HeqH) (esym H0) (esym H3) STEP_EQ).
           ++++ inversion STEP_EQ.
       +++ inversion STEP_EQ.
    ++ inversion STEP_EQ.
  + resolve_register regs0 STEP_EQ r to_nat.
    ++ destruct a as [w1 t1]. 
       resolve_memory_deep mem0 STEP_EQ w1.
       +++ destruct a as [old0 told0]. intro tageq. rewrite <- tageq in H0.
           resolve_register_deep regs0 STEP_EQ r0 to_nat.
           ++++ destruct a as [old1 told1]. intro tageq1. rewrite <- tageq1 in H3.
                apply (step_load Heqst (esym Heqnth) (esym HeqH) (esym H0) (esym H3) STEP_EQ). 
           ++++ inversion STEP_EQ.
       +++ inversion STEP_EQ.
    ++ inversion STEP_EQ.
  + resolve_register regs0 STEP_EQ r to_nat.
    ++ destruct a as [w1 t1]. 
       resolve_register_deep regs0 STEP_EQ r0 to_nat.
       +++ destruct a as [old0 told0]. intro tageq. rewrite <- tageq in H0.
           resolve_memory_deep mem0 STEP_EQ w1.
           ++++ destruct a as [old1 told1]. intro tageq1. rewrite <- tageq1 in H3.
                apply (step_store Heqst (esym Heqnth) (esym HeqH) (esym H0) (esym H3) STEP_EQ).
           ++++ inversion STEP_EQ.
       +++ resolve_memory_deep mem0 STEP_EQ w1 ; try (destruct a) ; inversion STEP_EQ.
    ++ inversion STEP_EQ.
  + resolve_register regs0 STEP_EQ r to_nat.
    ++ destruct a as [w1 t1]. 
       apply (step_jump Heqst (esym Heqnth) (esym HeqH) STEP_EQ).
    ++ inversion STEP_EQ.
  + resolve_register regs0 STEP_EQ r to_nat.
    ++ destruct a as [w1 t1].
       remember (if w1 == word_of_nat 0 then Some (nat_of_word pcv).+1 else find_label cd l) as save.
       unfold Option.bind, oapp, "==", nat_eqType, nat_eqMixin in STEP_EQ.
       remember ((if Equality.op (Equality.class (word_eqType (word_size mt))) w1 (word_of_nat 0)
               then Some (nat_of_word pcv).+1
                  else find_label cd l)) as pc'.
       cut (save = pc') ; try (rewrite Heqsave ; rewrite Heqpc' ; reflexivity). intro Heqif.
       rewrite Heqsave in Heqif. destruct pc'.
       +++ apply (step_bnz Heqst (esym Heqnth) (esym HeqH) (Heqif) STEP_EQ).
       +++ inversion STEP_EQ.
    ++ inversion STEP_EQ.
  + remember (l == alloc_label) as cond. destruct cond.
    (* l = alloc_label case *)
    ++ remember (@next_state_do_update st Symbolic.R Other ( RegWrite (inl R_RA) (word_of_nat((nat_of_word pcv).+1)))) as st_inter. 
       destruct st_inter ; simpl in STEP_EQ.
       +++ remember (alloc_fun cd s) as st_final. destruct st_final; simpl in STEP_EQ.
           ++++ resolve_memory_deep regs0 STEP_EQ 4.
                * intro eqa. destruct a as [old told]. inversion STEP_EQ.
                remember (regs0 (to_nat R_RA)) as rval. destruct rval.
                **  destruct a. unfold "==", nat_eqType, nat_eqMixin in Heqcond; simpl.
                    rewrite H3 in Heqst_final.
                    inversion Heqcond as [eq]. destruct (@eqnP l alloc_label) as [alloceq|].
                    *** apply (step_jal_alloc Heqst (esym Heqnth) (esym Heqrval) alloceq (esym Heqst_inter) (esym Heqst_final)). reflexivity.
                    *** inversion eq.
                **  rewrite <- eqa in H0. simpl in Heqrval.
                    unfold getm, getm_def in H0, Heqrval. simpl in Heqrval, H0.
                    rewrite <- Heqrval in H0. inversion H0.
                * inversion STEP_EQ.
           ++++ resolve_memory_deep regs0 STEP_EQ 4 ; (try destruct a) ; inversion STEP_EQ.
       +++ resolve_memory_deep regs0 STEP_EQ 4 ; (try destruct a) ; inversion STEP_EQ.
    (* l <> alloc_label case *)
    ++ simpl in STEP_EQ. resolve_memory_deep regs0 STEP_EQ 4 ; intro eq.
       +++ destruct a as [old told]. remember (find_label cd l) as pc'.
           cut (l <> alloc_label).
           ++++ intro ineq.
                destruct pc' as [pc'|].
                * rewrite H0 in eq. apply (step_jal Heqst (esym Heqnth) (esym eq) ineq Heqpc' STEP_EQ).
                * inversion STEP_EQ.
                  ++++ intro eql. remember (eq_op_to_eq l alloc_label) as equi.
                       destruct equi as [limp rimp]. rewrite <- (limp eql) in Heqcond.
                       inversion Heqcond.
       +++ inversion STEP_EQ.
    ++ inversion STEP_EQ.
  + inversion STEP_EQ.
Qed.

Theorem eval_step_equiv_step:
  forall cd st st' ev, (eval_step cd st = Some (st', ev)) <-> (step cd st st' ev).
  intros.
  split.
  + apply eval_step_sound.
  + apply eval_step_complete.
Qed.


Fixpoint execN (n: nat) (cde: code) (st: state) : option Z + nat :=
  match n with
  | O => inr 3
  | S n' =>
    match eval_step cde st with
    | None => (inl (
             do! w <- (regs st (to_nat R_COM));
             Some (Symbolic.convert (word.int_of_word (vala w)))))
    | Some (st', _) => execN n' cde st'
    end
  end.



Fixpoint fold_left {A B : Type} (f : B -> A -> B) (init : B) (l : list A) : B :=
  match l with
  | nil => init
  | cons e ll => fold_left f (f init e) ll
end.

Fixpoint fold_right {A B : Type} (f : B -> A -> B) (init : B) (l : list A) : B :=
  match l with
  | nil => init
  | cons e ll => f (fold_right f init ll) e
end.

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

(* code_lengths cde c give you the line at which the code of the compartment c begins*)
Definition memory_lengths (buf : NMap {fmap Block.id -> nat + seq value}):  NMap (NMap nat) :=
  (*
  (* this (notably) takes into account the fact that the allocation is linearized into 5 instructions *)
  let size_instr := (fun (i:Transitional.instr) => match i with | TrAlloc _ _ => 5 | TrLabel (_,Some _) => 2 | _ => 1 end) in
  let size_sum := (fold_left (fun n im => n + 1) 0) in
  let l := Maps.elementsm (mapm (fun m => mkfmap (size_sum (Maps.elementsm m))) buf) in
  mkfmap (fold_left_map (fun (count : nat) (p:nat*nat) => let (color, size) := p in ((color,count), count+size)) 0 l).*)

  let l := Maps.elementsm (mapm Maps.elementsm buf) in (* turns fmaps into lists *)
  let f := (fun acc => fold_left_map_bis (fun acc' (a : nat * (nat + seq value)) =>
                                     match (snd a) with
                                      | inl n => ((fst a, acc'), n + acc')
                                      | inr s => ((fst a, acc'), (size s) + acc') end
                      ) acc) in
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
    | TrLabel (l, None) => MrLabel (update_label l) :: nil
    | TrLabel (l, Some pl) => MrLabel (update_label l) :: (MrLabel (make_label pl)) :: nil
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

Definition transitional_to_merged (p: Intermediate.program) (cde : Transitional.code) : code :=
  let memory_size := memory_lengths (Intermediate.prog_buffers p) in
  let max_seq := (fun l => foldl Init.Nat.max 0 (map (fun p => match (fst p) with | TrLabel (la,_) => la | _ => 0 end) l )) in
  let lmax := foldl Init.Nat.max 0 (codomm(mapm max_seq cde)) in
  let max_seq := (fun l => foldl Init.Nat.max 0 (map (fun p => match (fst p) with | TrLabel (_,Some(_,p)) => p | _ => 0 end) l )) in
  let pmax := foldl Init.Nat.max 0 (codomm(mapm max_seq cde)) in
  let cmax := foldl Init.Nat.max 0 (domm cde) in
  let make_label := (fun pl => lmax * (cmax + 1) + 1 + (fst pl)*pmax + (snd pl)) in
  let update_label := (fun c old => old + lmax * (c)) in
  let f := (fun  (itrt: Transitional.instr * mem_tag) (c: code) =>
    let (itr, t) := itrt in
    let il := map (fun i => (i,t)) (instr_translation make_label (update_label (color t)) memory_size itr) in app il c) in
  let c :=  flatten(map snd  (Maps.elementsm cde)) in
  foldr f nil c.

Definition inital_memory (p : Intermediate.program) :=
  let p := Linearize.linearize p in
  let bufs := Linearize.buffers p in
    let base_adress c b :=
     (*  length of code + 1 + number of triples (c',b',_) such that (c', b') that occur before (c, b) *)
      (*length (Linearize.procedures p) + 1 +*)
      length (domm (filterm (fun x _ => match x with (c', b', _) => (c' < c) || ((c' == c) && (b' < b)) end)
                     (* TL TODO codomm doesn't typecheck... *)
                     (* Invariant: Linearize.buffers is "continuous" *)
                     ((Linearize.buffers p))))
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

Definition reg0 : registers :=
  let default_reg := (word_of_nat 0)@(LRC.Other): atom (tag_type Symbolic.R) in
  [fmap (0, default_reg) ;
   (1, default_reg) ;
   (2, default_reg) ;
   (3, default_reg) ;
   (4, (word_of_nat (2 ^ 15))@(LRC.Other)) ; (* value equivalent to "Undef" for R_RA*)
   (5, default_reg) ;
   (6, default_reg) ;
   (16,default_reg) ;
   (17,default_reg) ;
   (18,default_reg) ;
   (19,default_reg) ].

Definition run_merged cd mem0 fuel nc :=
  let pctag := build_tpc 0 in
      execN fuel cd {|mem := mem0 ; regs := reg0 ; pc := (word_of_nat 0)@pctag ; comp_num := nc|}.


Definition compile_run_merged fuel (p : Intermediate.program) :=
 run_merged (transitional_to_merged p (pre_linearize p)) (inital_memory p) fuel (1+ Nat.log2 (size (domm (Intermediate.prog_interface p)))).

Close Scope monad_scope.


Definition compile_and_run_from_source_merged := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p => compile_run_merged fuel compiled_p
| None => inl None
end.


End WithClasses.


Definition compile_and_run_from_source_merged_ex (mt : machine_types) := 
fun (p : Source.program) (fuel : nat) =>
match Compiler.compile_program p with
| Some compiled_p =>
    match @compile_run_merged mt fuel compiled_p with
    | inl (Some n) => print_ocaml_int (z2int n)
    | inl None => print_error ocaml_int_1
    | inr n => print_error (nat2int n)
    end
| None => print_error ocaml_int_0
end.



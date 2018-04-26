From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq ssrint.
From CoqUtils Require Import hseq.

Require Import Common.Definitions.
Require Import MicroPolicies.Utils MicroPolicies.Types MicroPolicies.Symbolic MicroPolicies.Exec.


(** Tags **)

(* TL TODO: this mechanism of value tag and location tag moy be generalized *)

Inductive value_tag : Type := Ret : nat -> value_tag | Other : value_tag.

Module Import ValueTagEq.
Definition option_of_value_tag t :=
  match t with
  | Other => None
  | Ret n => Some n
  end.

Definition value_tag_of_option t :=
  match t with
  | None => Other
  | Some n => Ret n
  end.

Lemma option_of_value_tagK : cancel option_of_value_tag value_tag_of_option.
Proof. by case. Qed.

Definition value_tag_eqMixin := CanEqMixin option_of_value_tagK.
Canonical value_tag_eqType := EqType value_tag value_tag_eqMixin.
End ValueTagEq.

Inductive pc_tag : Type := Level : nat -> pc_tag.

Module Import PCTagEq.
Definition nat_of_pc_tag t :=
  match t with
  | Level n => n
  end.

Definition pc_tag_of_nat n := Level n.

Lemma nat_of_pc_tagK : cancel nat_of_pc_tag pc_tag_of_nat.
Proof. by case. Qed.

Definition pc_tag_eqMixin := CanEqMixin nat_of_pc_tagK.
Canonical pc_tag_eqType := EqType pc_tag pc_tag_eqMixin.
End PCTagEq.

Record mem_tag : Type := MTag {
  vtag  : [eqType of value_tag];
  color : Component.id;
  entry : list Component.id;
}.


Definition def_mem_tag (c : Component.id) : mem_tag :=
  {| vtag := Other ;
     color := c ;
     entry := [:: ]
  |}.



Module Import MemTagEq.
Definition tuple_of_mem_tag t := (vtag t, color t, entry t).
Definition mem_tag_of_tuple tp :=
  match tp with
  | (vt, c, e) => MTag vt c e
  end.

Lemma tuple_of_mem_tagK : cancel tuple_of_mem_tag mem_tag_of_tuple.
Proof. by case. Qed.

Definition mem_tag_eqMixin := CanEqMixin tuple_of_mem_tagK.
Canonical mem_tag_eqType := EqType mem_tag mem_tag_eqMixin.
End MemTagEq.

Import Symbolic.

Definition lrc_tags := {|
  pc_tag_type    := [eqType of pc_tag];
  reg_tag_type   := [eqType of value_tag];
  mem_tag_type   := [eqType of mem_tag];
  entry_tag_type := [eqType of unit];
|}.


(** Tag propagation rules **)

Import DoNotation.


Definition belong (c : Component.id) (m : tag_type lrc_tags M) : bool :=
  match m with
    | {| color := c'  |} => c == c'
  end.

Definition check_belong (c : Component.id) (m : tag_type lrc_tags M) : option unit :=
  match belong c m with
    | true => Some tt
    | false => None
  end.


Definition check_ret (n : nat) (r : tag_type lrc_tags R) : option unit :=
  match r with
    | Ret n' => if n == n' then Some tt else None
    | Other => None
  end.

Definition check_entry (c : Component.id) (m : tag_type lrc_tags M) : option unit :=
  match m with
    | {| entry := l |} => if mem_seq l c then Some tt else None
  end.


Definition switch_val (m : tag_type lrc_tags M)
           (v : tag_type lrc_tags R) : (tag_type lrc_tags M * tag_type lrc_tags R) :=
  match m with
    | {| vtag := v' ; color := c ; entry := e |} => ({| vtag := v ; color := c ; entry := e |}, v')
  end.


(* TL TODO: without this, I get a type error *)
Definition build_tpc (n : nat) : tag_type lrc_tags P := Level n.

(* TL TODO: comments? cf org file *)
Definition instr_rules (op : opcode)
           (tpc : tag_type lrc_tags P)
           (ti : tag_type lrc_tags M)
           (ts : hseq (tag_type lrc_tags) (inputs op))
           (tni : tag_type lrc_tags M) : option (ovec lrc_tags op) :=
  let current := match ti with {| color := c |} => c end in
  let level := match tpc with Level n => n end in
  match op, ts return option (ovec _ op) with
  | NOP,     [hseq]            => do! _ <- check_belong current tni;
                                     Some (OVec NOP       tpc [hseq])

  | CONST,   [hseq td]         => do! _ <- check_belong current tni;
                                     Some (OVec CONST     tpc [hseq Other])

  | MOV,     [hseq ts; td]     => do! _ <- check_belong current tni;
                                     Some (OVec MOV       tpc [hseq Other; ts])

  | BINOP b, [hseq tx; ty; td] => do! _ <- check_belong current tni;
                                     Some (OVec (BINOP b) tpc [hseq tx; ty; Other])

  | LOAD,    [hseq tp; ts; td] => do! _ <- check_belong current tni;
                                     if belong current ts then
                                       let (ts', td') := switch_val ts Other in
                                       Some (OVec LOAD tpc [hseq tp; ts'; td'])
                                     else
                                       Some (OVec LOAD tpc [hseq tp; ts; Other])

  | STORE,   [hseq tp; ts; td] => do! _ <- check_belong current tni;
                                 do! _ <- check_belong current td;
                                     let (td', _) := switch_val td ts in
                                     Some (OVec STORE tpc [hseq tp; Other; td'])

  | BNZ,     [hseq tx]         => do! _ <- check_belong current tni;
                                     Some (OVec BNZ       tpc [hseq tx])

  | JUMP,    [hseq tp]         => if belong current tni then
                                   Some (OVec JUMP tpc [hseq tp])
                                 else
                                   (* TL TODO: should forbid return if level = 0 ?         *)
                                   (*          I think it is already enforced by invariant *)
                                   (*          (unique Ret n)                              *)
                                   do! _ <- check_ret level.-1 tp;
                                       Some (OVec JUMP (build_tpc level.-1) [hseq Other])

  | JAL,     [hseq tra]    => if belong current tni then
                                   Some (OVec JAL tpc [hseq tra])
                                 else
                                   do! _ <- check_entry current tni;
                                       Some (OVec JAL (build_tpc level.+1) [hseq Ret level])

  | _,     _                   => None
  end.



Definition transfer (iv : ivec lrc_tags) : option (vovec lrc_tags (op iv)) :=
  match iv with (* TL TODO: ask someone obout this dependent boilerplate *)
  | IVec vop tpc ti ts tni =>
    match vop, ts, ti, tni return option (vovec _ vop) with
    | (OP op), ts, ti, Some tni => instr_rules op tpc ti ts tni
    (* Monitor stuff *)
    | SERVICE, [hseq], ti, None => Some tt
    |       _,      _,  _,    _ => None
    end
  end.



(** Instance **)

Global Instance sym_lrc : params := {
  ttypes := lrc_tags;
  transfer := transfer;
  internal_state := [eqType of unit]
}.



(** Syscalls **)

From CoqUtils Require Import word.

Section WithClasses.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {sregs : syscall_regs mt}.
(* TL TODO: these notations inside a module? *)

Notation state := (@Symbolic.state mt sym_lrc).
Notation State := (@Symbolic.State mt sym_lrc).

Definition ratom := (atom (mword mt) value_tag).
Definition matom := (atom (mword mt) mem_tag).

(* alloc is a syscall taking one argument, the size to allocate *)
(* a syscall don't change the pc level *)
Definition alloc_fun (st : state) : option state :=
  (* TL TODO: Rely on the fact that it set implem is a sorted list, kinda fishy *)
  let max_addr := last (domm (mem st)) (as_word 0) in
  do! ra <- regs st ra;
  (* TL TODO: Is using return address to compute calling component safe? *)
  let current_c := do! atom <- mem st (vala ra);
                   Some (color (taga atom)) in
  (* create the new bloc *)
  let atom : matom := (word.as_word 0)@(def_mem_tag current_c) in
  do! size <- regs st syscall_arg1;
  do! length <- match word.int_of_word (vala size) with
                | Posz x => Some x
                | Negz _ => None
                end;
  let bloc :=
      mkseq (fun n => ((word.addw max_addr (word.as_word (n + 1))), atom))
            length in
  let mem' := unionm (mem st) (mkfmap bloc) in
  (* return *)
  do! addr <- (do! x <- head bloc;
                 Some (fst x));
  do! regs' <- updm (regs st) syscall_ret addr@Other;
  let pc' := (vala ra)@(taga (pc st)) in
  Some (State mem' regs' pc' tt).

End WithClasses.
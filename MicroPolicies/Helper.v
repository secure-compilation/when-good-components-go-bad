Require Import Common.Definitions CompCert.Events.
From QuickChick Require Import Show.

From CoqUtils Require Import hseq word.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import MicroPolicies.Utils MicroPolicies.Types MicroPolicies.Symbolic MicroPolicies.LRC.
Require Import Intermediate.Machine.
Require Import I2MP.Examples.Helper Merged Int32 Instance.

Require Export Extraction.Definitions.
Require Import CompCert.Events.
Export Symbolic.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DoNotation.

Require Import String.
Open Scope string.


Fixpoint execN_trace {mt ops sp table} (n: nat) (st: Symbolic.state sp) : trace :=
  match n with
  | O => []
  | S n' =>
    match (@Exec.stepf mt ops sp table) st with
    | None => []
    | Some (st', None) => @execN_trace mt ops sp table n' st'
    | Some (st', Some ev) => ev :: (@execN_trace mt ops sp table n' st')
    end
  end.

Definition instr_rules_empty (rcom_val : Z)
  (op : opcode)
  (tpc : tag_type lrc_tags P)
  (ti : tag_type lrc_tags M)
  (ts : hseq (tag_type lrc_tags) (outputs op))
  (tni : option (tag_type lrc_tags M)) : option (ovec lrc_tags op * option event) :=
  let current := match ti with {| color := c |} => c end in
  let level := match tpc with Level n => n end in
  match op, ts return option (ovec _ op * option event) with
  | JUMP,    _  => if belong current tni then
                    Some (OVec JUMP tpc ts, None)
                  else
                    let ev := do! c' <- get_tni_color tni;
                              Some (ERet current (rcom_val) c') in
                    Some (OVec JUMP tpc ts, ev)

  | JAL,     _  => if belong current tni then
                    Some (OVec JAL tpc ts, None)
                  else
                    let ev := do! c' <- get_tni_color tni;
                              do! p  <- get_proc_name tni;
                              Some (ECall current p (rcom_val) c') in
                    Some (OVec JAL tpc ts, ev)
  | NOP,     _    => Some (OVec NOP tpc ts, None)
  | CONST,     _    => Some (OVec CONST tpc ts, None)
  | MOV,     _    => Some (OVec MOV tpc ts, None)
  | BINOP b,     _    => Some (OVec (BINOP b) tpc ts, None)
  | LOAD,     _    => Some (OVec LOAD tpc ts, None)
  | STORE,     _    => Some (OVec STORE tpc ts, None)
  | BNZ,     _    => Some (OVec BNZ tpc ts, None)
  | _,     _    => None
  end.

Definition transfer_empty (iv : Symbolic.ivec lrc_tags) (evi : Symbolic.ev_inputs) : option (Symbolic.vovec lrc_tags (Symbolic.op iv) * option event) :=
  match iv with (* TL TODO: ask someone obout this dependent boilerplate *)
  | Symbolic.IVec vop tpc ti ts tni =>
    match vop, ts, ti, tni return option (Symbolic.vovec _ vop * option event) with
    | (OP op), ts, ti, tni =>
        do! out:((ovec _ op) * option event) <- instr_rules_empty (Symbolic.rcom_value evi) tpc ti ts tni;
        let (ov, ev) := out in
        Some (Symbolic.OVec op (trpc ov) (tr ov), ev)
    (* Monitor stuff *)
    | SERVICE, [hseq], ti, None => Some (tt, None)
    |       _,      _,  _,    _ => None
    end
  end.


Definition sym_empty : Symbolic.params :=
  {|
    Symbolic.ttypes := lrc_tags;
    Symbolic.transfer := transfer_empty;
    Symbolic.internal_state := [eqType of unit]
  |}.

Definition alloc_fun (st : @Symbolic.state mt sym_empty) : option (Symbolic.state sym_empty) :=
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
  Some (Symbolic.State sym_empty mem' regs' next_pc tt (Symbolic.comp_num st)).


Definition table_empty : (Symbolic.syscall_table sym_empty) :=
  [fmap ((word_of_nat alloc_label), (@Symbolic.Syscall mt sym_empty tt alloc_fun ) )].

Definition mt := concrete_int_32_mt.
Global Instance ops : machine_ops mt := concrete_int_32_ops.


Definition nc := let component_count := 2 in (1+ Nat.log2 (1 + component_count)).

Definition initial_state {tf} : (@state mt ({| ttypes := lrc_tags; transfer := tf; internal_state := [eqType of unit] |} )) :=
  let pctag := build_tpc 0 in
  @State mt {| ttypes := lrc_tags; transfer := tf; internal_state := [eqType of unit] |}
         emptym Merged.reg0 ((word_of_nat 0)@pctag) tt nc.

Definition get_trace_no_mp := @execN_trace mt ops sym_empty table_empty 1000.
Definition get_trace_merged := @execN_trace mt ops sym_lrc_merged Merged.table 1000.


(*
Definition initial_state {tf} : (@state mt ({| ttypes := lrc_tags; transfer := tf; internal_state := [eqType of unit] |} )) :=
  let pctag := build_tpc 0 in
  @State mt {| ttypes := lrc_tags; transfer := tf; internal_state := [eqType of unit] |}
         emptym Merged.reg0 ((word_of_nat 0)@pctag) tt nc.
*)

Instance showValue : Show event :=
  {
    show e := match e with
              | ECall c p z c' => "call " ++ (show c) ++ " -> " ++ (show c') ++ " ; "
                                   ++ (show p) ++ " ( " ++ (show z ) ++ " )"
              | ERet c z c' => "ret "  ++ (show c) ++ " -> " ++ (show c') ++ " ; "
                                ++ " ( " ++ (show z ) ++ " )"
              end
  }.

Definition event_eq (a b : event) : bool :=
  match (a, b) with
  | (ECall ca pa za cca, ECall cb pb zb ccb) =>
      andb (andb (ca == cb) (pa == pb)) (andb (Z.eqb za zb) (cca == ccb) )
  | (ERet ca za cca, ERet cb zb ccb) =>
      andb (andb (ca == cb) (Z.eqb za zb)) (cca == ccb)
  | _ => false
  end.
             
(*
Definition even_mixin : Equality.mixin_of event.
  apply (@Equality.Mixin _ event_eq).
  unfold Equality.axiom. intros.
  remember (event_eq x y) as eq eqn:Heq. destruct eq.
  + unfold event_eq in Heq. destruct x,y ; try (inversion Heq ; done).
    apply ReflectT. unfold andb in Heq.
    *)
Definition trace_eq m t : bool :=
  andb ((size m) == (size t))
       (foldl (fun acc '(l, r) => andb acc (event_eq l r) ) true (zip m t)).

Definition run_test c0 p0 c1 p1 := 
  let m0_merged := (get_trace_merged (app c0 p0) initial_state) in
  let m1_merged := (get_trace_merged (app c1 p1) initial_state) in
  let m2_merged := (get_trace_merged (app c0 p1) initial_state) in
  
  let m0_empty := (get_trace_no_mp (app c0 p0) initial_state) in
  let m1_empty := (get_trace_no_mp (app c1 p1) initial_state) in
  let m2_empty := (get_trace_no_mp (app c0 p1) initial_state) in
  (*
  printer (
      "---------------------------" ++ newline ++
          (show m0_merged) ++ newline ++
          (show m1_merged) ++ newline ++
          (show m2_merged) ++ newline ++
          (show m0_empty) ++ newline ++
          (show m1_empty) ++ newline ++
          (show m2_empty) ++ newline ++
      "---------------------------" ++ newline)
   *) (
  if (trace_eq m0_merged m1_merged)
  then if(trace_eq m0_empty m1_empty)
       then if (trace_eq m0_merged m2_merged)
            then if (trace_eq m0_empty m2_empty)
                 then "test failed (c)"
                 else "test successful"
            else "recomposition breaked in merged"
       else "test failed (b)"
  else "test failed (a)"
    ).

Definition mt := concrete_int_32_mt.

(* run ops, then jump to 10 *)
Definition context ops :=
  (@MrLabel mt 0) :: (MrConst (word_of_nat 0) R_COM) :: (app ops [MrJal 10 ; MrHalt]).

Definition alloc n := [:: (@MrConst mt (word_of_nat n) (R_SP)) ;
                       (MrMov (inl R_SP) (inr R_SC_ARG1)) ;
                       (MrMov (inl R_RA) (inr R_SC_ARG3))  ;
                       (MrJal alloc_label)  ;
                       (MrMov (inr R_SC_ARG3) (inl R_RA))  ;
                       (MrMov (inr R_SC_RET) (inl R_SP))].

(* give tag for component cnum to a list of code *)
(* with the first instruction being an entry point *) 
Definition give_tag cl cnum pid : @code mt :=
  let tag := map (fun i => (i, MTag Other cnum None true)) in
  match cl with
  | top :: cll => (top, MTag Other cnum (Some (pid, [0 ; 1])) true) :: (tag cll)
  | nil => nil
  end.

Definition ret n := [@MrConst mt (word_of_nat n) R_COM; MrJump R_RA].

Definition p_bnz ops r :=
  (@MrLabel mt 10) :: (app ops (app
    ((MrBnz r 20) :: (ret 0))
    ((MrLabel 20) :: (ret 1)) )).

(* cross-compartment loading *)
Definition test1 := run_test
                      (give_tag (context (alloc 20)) 0 0)
                      (give_tag ([@MrLabel mt 10 ; MrHalt]) 1 0)
                      (give_tag (context []) 0 0)
                      (give_tag (app
                                  [@MrLabel mt 10 ;
                                  MrConst (word_of_nat 1) R_SP ;
                                  MrConst (word_of_nat 2) R_ONE]
                                  (app (nseq ((word_size mt) - nc)
                                            (MrBinop Mul R_SP R_ONE R_SP)) (* bitshift *)
       [MrBinop Add R_SP R_ONE R_SP; MrLoad R_SP R_SP ; MrJump R_RA])) 1 0).

(* cross-compartment return adress *)
Definition test2 := run_test
                      (give_tag (context [MrNop]) 0 0)
                      (give_tag ((MrLabel 10) :: (MrConst zerow R_ONE) ::
                                   (MrBinop Add R_RA R_ONE R_RA) :: (ret 0)) 1 0)
                      (give_tag (context []) 0 0)
                      (give_tag ([MrLabel 10 ;
                                  MrConst (word_of_nat 3) R_COM ; MrBinop Minus R_RA R_COM R_COM ;
                                  MrJump R_RA
                         ]) 1 0).
                      (*
                      (give_tag (p_bnz [MrJal 5 ; MrConst (word_of_nat 9) R_COM ;
                                        MrBinop Minus R_RA R_COM R_COM] R_COM) 1 0). *)

(* intra-compartment return adress *)
Definition test3 := run_test
                      (give_tag (context [MrNop]) 0 0)
                      (give_tag ((MrLabel 10) :: (MrConst zerow R_ONE) ::
                                   (MrBinop Add R_RA R_ONE R_RA) :: (ret 0)) 1 0)
                      (give_tag (context []) 0 0)
                      (give_tag ([MrLabel 10 ; MrMov (inl R_RA) (inl R_SP) ; MrJal 15; MrLabel 15;
                                  MrConst (word_of_nat 7) R_COM ; MrBinop Minus R_RA R_COM R_COM ;
                                  MrJump R_SP
                         ]) 1 0).
(*
                      (give_tag (p_bnz [MrJal 15;MrLabel 15; MrConst (word_of_nat 9) R_COM ;
                                        MrBinop Minus R_RA R_COM R_COM] R_COM) 1 0). *)


(* call/return clearing *)
Definition test4 := run_test
                      (give_tag (context (alloc 20)) 0 0)
                      (give_tag ((MrLabel 10) :: (MrConst zerow R_ONE) ::
                                   (MrBinop Add R_RA R_ONE R_RA) :: (ret 0)) 1 0)
                      (give_tag (context []) 0 0)
                      (give_tag (p_bnz [] R_SP) 1 0).

Definition to_run :=
  printer ("test 1:" ++ newline ++ test1)
  printer ("test 2:" ++ newline ++ test2)
  printer ("test 3:" ++ newline ++ test3)
  printer ("test 4:" ++ newline ++ test4)
  printer newline tt.


Set Warnings "-extraction-reserved-identifier".
Extraction "/tmp/run_recomposition_merged_test.ml" to_run.

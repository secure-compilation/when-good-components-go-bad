Require Import Common.Definitions CompCert.Events.
From QuickChick Require Import Show.

From CoqUtils Require Import hseq word.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import MicroPolicies.Utils MicroPolicies.Types MicroPolicies.Symbolic MicroPolicies.LRC.
Require Import Intermediate.Machine.
Require Import I2MP.Examples.Helper MicroPolicies.Int32 MicroPolicies.Merged.

Require Export Extraction.Definitions.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DoNotation.

Require Import String.
Open Scope string.

Definition instr_rules_empty (rcom_val : Z)
  (op : opcode)
  tpc
  ti
  (ts : hseq _ (inputs op))
  tni
  : option ((ovec op) * (option event)) :=
  let current := match ti with {| color := c |} => c end in
  let level := match tpc with Level n => n end in
  match op, ts return option (ovec op * option event) with
  | JUMP,    _  => if belong current tni then
                    Some (OVec tpc ts, None)
                  else
                    let ev := do! c' <- get_tni_color tni;
                              Some (ERet current (rcom_val) c') in
                    Some (OVec tpc ts, ev)

  | JAL,     _  => if belong current tni then
                    Some (OVec tpc ts, None)
                  else
                    let ev := do! c' <- get_tni_color tni;
                              do! p  <- get_proc_name tni;
                              Some (ECall current p (rcom_val) c') in
                    Some (OVec tpc ts, ev)
  | _,     _    => Some (OVec tpc ts, None)
  end.

Definition get_trace_merged := @Merged.execN_trace concrete_int_32_mt instr_rules 1000.
Definition get_trace_no_mp := @Merged.execN_trace concrete_int_32_mt instr_rules_empty 1000.

Definition nc := let component_count := 2 in (1+ Nat.log2 (1 + component_count)).
Definition initial_state : @state concrete_int_32_mt :=
  let pctag := build_tpc 0 in
  {|mem := emptym ; regs := reg0 ; pc := (word_of_nat 0)@pctag ; comp_num := nc|}.


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
  let tag := map (fun i => (i, MTag Other cnum None)) in
  match cl with
  | top :: cll => (top, MTag Other cnum (Some (pid, [0 ; 1]))) :: (tag cll)
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

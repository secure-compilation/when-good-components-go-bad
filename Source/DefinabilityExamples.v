Require Import Lib.Extra.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import Common.Traces.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.Definability.

From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq.
From mathcomp Require ssrnat.

Import Source.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".
Local Open Scope fset_scope.

(** Checking flattening of expressions*)
(* Quick sanity check (unrealistic) *)
Example test_E_seq_of_list_expr :
  let list_expr := [E_val (Int 0); E_val (Int 1); E_val (Int 2)] in
  let seq_expr  := E_seq (E_val (Int 0))
                         (E_seq (E_val (Int 1))
                                (E_val (Int 2))) in
  E_seq_of_list_expr list_expr = Some seq_expr.
Proof. reflexivity. Qed.

Example test_E_seq_of_list_expr' :
  let list_expr := [E_val (Int 0); E_val (Int 1); E_val (Int 2)] in
  let seq_expr  := E_seq (E_seq (E_val (Int 0))
                                (E_val (Int 1)))
                         (E_val (Int 2)) in
  E_seq_of_list_expr' list_expr = Some seq_expr.
Proof. reflexivity. Qed.


(** Checking back-translation of assignments *)
(* I find that checking fmap membership, even for map with given static data,
     is a bit of a pain. It would be nice to add these to the 'done' tactical or
     some other automation mean *)
Example setm_fmap_membership :
  let fmap_thing := [fmap (0, false); (1, false); (2, false)] in
  let fset_thing := [fset 0; 1; 2] in
  1 \in domm fmap_thing /\ false \in codomm fmap_thing /\ 1 \in fset_thing.
Proof.
  simpl. split.
  (* Not automated yet *)
  all: simpl; try done.
  (* \in domm of something is usually solved automatically once mem_domm has
         been used *)
  rewrite mem_domm ; done. Undo.
  (* I guess dommP(n) can be used too *)
  apply /dommP. eexists. done.
  split.

  (* codomm is a bit more subtle, either use codommP(n) *)
  apply /codommP ; exists 1 ; done. Undo. (* Not automatic so not really useful *)
  (* eexists doesn't help much : in the previous case we had m k = some ?v,
       there we have  m ?k = some v, which is less trivial *)
  apply /codommP ; eexists. Undo.
  (* Rewriting codomm with its definition works much better *)
  rewrite /codomm. rewrite /invm. simpl. (* from there, its' just as with domm *)
  apply /dommP ; eexists ; done. Undo.
  rewrite mem_domm ; done.

    (* Since [fset a1; .. ; an ] is a notation for nested (fsetU (fset a1) ..
       (fsetU (fset an))), we can rewrite it easily *)
    by rewrite !in_fsetU1.
Qed.

(* In the meantime, let's use these notations for examples *)
Tactic Notation "find_in_domm" :=
  rewrite mem_domm.
Tactic Notation "find_in_domm_goal" :=
  apply /dommP ; eexists.
Tactic Notation "find_in_codomm" :=
  rewrite /codomm ; rewrite /invm ; simpl ;
  find_in_domm.
Tactic Notation "find_in_codomm_goal" int_or_var(n) :=
  apply /codommP ; exists n.
Tactic Notation "find_in_fset" :=
  rewrite !in_fsetU1.


Example test_prefill_read_aux0 :
  let '(C1,P1) := (1,1) in
  let '(arg1, ret1) := (17%Z, 42%Z) in
  let '(off0, load0, off1, load1, off2, load2) := (0%Z, Int 17%Z, 1%Z, Int 420%Z, 2%Z, Int 1337%Z) in
  let ev1 := ECall Component.main P1 arg1 C1 in
  let ev1':= ELoad C1 off0 load0 Component.main in
  let ev2 := ERet C1 ret1 Component.main in
  let ev3 := ELoad Component.main off1 load1 C1 in
  let ev4 := ELoad Component.main off2 load2 C1 in
  let acc := [] in
  let offsets := indexes_read_init in
  prefill_read_aux Component.main [  ev1'; ev2;  ev3 ; ev4 ] acc offsets  = [(assign_public off0 load0)] /\
  prefill_read_aux_ntr Component.main [  ev1'; ev2;  ev3 ; ev4 ] offsets  = [(assign_public off0 load0)]
.
Proof. by []. Qed.

Example test_prefill_read_aux1 :
  let '(C1,P1) := (1,1) in
  let '(arg1, ret1) := (17%Z, 42%Z) in
  let '(off0, load0, off1, load1, off2, load2) := (0%Z, Int 17%Z, 1%Z, Int 420%Z, 2%Z, Int 1337%Z) in
  let ev1 := ECall Component.main P1 arg1 C1 in
  let ev1':= ELoad C1 off0 load0 Component.main in
  let ev2 := ERet C1 ret1 Component.main in
  let ev3 := ELoad Component.main off1 load1 C1 in
  let ev4 := ELoad Component.main off2 load2 C1 in
  let acc := [] in
  let offsets := indexes_read_init in
  prefill_read_aux Component.main [  ev3 ; ev4 ] acc offsets  = []
  /\ prefill_read_aux_ntr Component.main [  ev3 ; ev4 ] offsets  = [].
Proof. by []. Qed.

Example test_prefill_read_aux2 :
  let '(C1,P1) := (1,1) in
  let '(arg1, ret1) := (17%Z, 42%Z) in
  let '(off1, load1, off2, load2) := (1%Z, Int 420%Z, 2%Z, Int 1337%Z) in
  let ev1 := ECall Component.main P1 arg1 C1 in
  let ev2 := ERet C1 ret1 Component.main in
  let ev3 := ELoad Component.main off1 load1 C1 in
  let ev4 := ELoad Component.main off2 load2 C1 in
  let acc := [] in
  let offsets := indexes_read_init in
  prefill_read_aux C1 [ ev3 ; ev4 ] acc offsets = [(assign_public 2 (Int 1337)); (assign_public 1 (Int 420))] /\
  prefill_read_aux_ntr C1 [ ev3 ; ev4 ] offsets = [ (assign_public 1 (Int 420)); (assign_public 2 (Int 1337))].
Proof. by []. Qed.

Example test_prefill_read_tricky :
  let '(C1,P1,C2,P2) := (1,1,2,2) in
  let Pintf := [fmap
                  (Component.main, Component.mkCompInterface fset0 [fset (C1, P1)] 3  );
                  (C1, Component.mkCompInterface [fset P1] [fset (C2, P2)] 3 );
                  (C2, Component.mkCompInterface [fset P2] [fset (C1, P1)] 3 )] in
  (* we are not interested in call args and return values *)
  let '(arg, ret) := (17%Z, 42%Z) in
  let '(load1, load2, load3, load4,
        load5, load6, load7, load8,
        load9, load10, load11, load12,
        load13, load14) := (Int 1%Z, Int 2%Z, Int 3%Z, Int 4%Z,
                            Int 5%Z, Int 6%Z, Int 3%Z, Int 8%Z,
                            Int 5%Z, Int 10%Z, Int 3%Z, Int 12%Z,
                            Int 13%Z, Int 14%Z) in
  let '(off1, off2, off3, off4,
        off5, off6, off7, off8,
        off9, off10, off11, off12,
        off13, off14) :=  (0%Z, 0%Z, 0%Z, 1%Z,
                           1%Z, 0%Z, 0%Z, 1%Z,
                           1%Z, 1%Z, 0%Z, 0%Z,
                           1%Z, 1%Z) in
  let load_ev1 := ELoad Component.main off1 load1 C1 in
  let load_ev2 := ELoad Component.main off2 load2 C2 in
  let call_ev1 := ECall Component.main P1 arg C1 in

  let load_ev3 := ELoad C1 off3 load3 Component.main in
  let load_ev4 := ELoad C1 off4 load4 C2 in
  let call_ev2 := ECall C1 P2 arg C2 in

  let load_ev5 := ELoad C2 off5 load5 Component.main in
  let load_ev6 := ELoad C2 off6 load6 C1 in
  let call_ev3 := ECall C2 P1 arg C1 in

  let load_ev7 := ELoad C1 off7 load7 Component.main in
  let load_ev8 := ELoad C1 off8 load8 C2 in
  let ret_ev1  := ERet C1 ret C2 in

  let load_ev9 := ELoad C2 off9 load9 Component.main in
  let load_ev10:= ELoad C2 off10 load10 C1 in
  let ret_ev2  := ERet C2 ret C1 in

  let load_ev11:= ELoad C1 off11 load11 Component.main in
  let load_ev12:= ELoad C1 off12 load12 C2 in
  let ret_ev3  := ERet C1 ret Component.main in

  let load_ev13:= ELoad Component.main off13 load13 C1 in
  let load_ev14:= ELoad Component.main off14 load14 C2 in

  let acc := [::] in
  let offsets := indexes_read_init in
  let cst :=  fun (C: Component.id) (t: trace) =>
                filter (fun e => (C == cur_comp_of_event e) ||
                              match e with
                              | ELoad _ _ _ C => true
                              | _ => false end) t in
  let trace := [load_ev1;  load_ev2;  call_ev1;
                load_ev3;  load_ev4;  call_ev2;
                load_ev5;  load_ev6;  call_ev3;
                load_ev7;  load_ev8;  ret_ev1;
                load_ev9;  load_ev10;  ret_ev2;
                load_ev11;  load_ev12;  ret_ev3;
                load_ev13;  load_ev14] in
  (* be careful to not have too many suffixes! suffixes_of_trace (or _seq)
       produces all of them ! *)
  let sfx1 := [ load_ev3;  load_ev4;  call_ev2;
                load_ev5;  load_ev6;  call_ev3;
                load_ev7;  load_ev8;  ret_ev1;
                load_ev9;  load_ev10;  ret_ev2;
                load_ev11;  load_ev12;  ret_ev3;
                load_ev13;  load_ev14] in
  let sfx2 := [ load_ev5;  load_ev6;  call_ev3;
                load_ev7;  load_ev8;  ret_ev1;
                load_ev9;  load_ev10;  ret_ev2;
                load_ev11;  load_ev12;  ret_ev3;
                load_ev13;  load_ev14] in
  let sfx3 := [ load_ev7;  load_ev8;  ret_ev1;
                load_ev9;  load_ev10;  ret_ev2;
                load_ev11;  load_ev12;  ret_ev3;
                load_ev13;  load_ev14] in
  let sfx4 := [ load_ev9;  load_ev10;  ret_ev2;
                load_ev11;  load_ev12;  ret_ev3;
                load_ev13;  load_ev14] in
  let sfx5 := [ load_ev11;  load_ev12;  ret_ev3;
                load_ev13;  load_ev14] in
  let sfx6 := [ load_ev13;  load_ev14] in
  let '(ssfx1, ssfx2,
        ssfx3, ssfx4, ssfx5, ssfx6) :=
      (cst Component.main sfx1, cst C1 sfx2,
       cst C2 sfx3, cst C1 sfx4, cst C2 sfx5, cst C1 sfx6 ) in
  let st0 := stack_state0 in
  let st1 := StackState C1 [Component.main] in
  let st2 := StackState C2 [C1; Component.main] in
  let st3 := StackState C1 [C2; C1; Component.main] in
  let st4 := StackState C2 [C1; Component.main] in
  let st5 := StackState C1 [Component.main] in
  all (well_formed_event Pintf) trace /\
  (well_bracketed_trace st0 (call_ev1::sfx1) /\
   prefill_read_aux Component.main ssfx1 acc offsets =
   [(assign_public off5 load5); (assign_public off3 load3)] /\
   prefill_read_aux_ntr Component.main ssfx1 offsets =
   [(assign_public off3 load3); (assign_public off5 load5)]) /\
  (well_bracketed_trace st1 (call_ev2::sfx2) /\
   prefill_read_aux C1 ssfx2 acc offsets = [(assign_public off6 load6)] /\
   prefill_read_aux_ntr C1 ssfx2 offsets = [(assign_public off6 load6)]) /\
  (well_bracketed_trace st2 (call_ev3::sfx3) /\
   prefill_read_aux C2 ssfx3 acc offsets  = [(assign_public off8 load8)] /\
   prefill_read_aux_ntr C2 ssfx3 offsets  = [(assign_public off8 load8)]) /\
  (well_bracketed_trace st3 (ret_ev1::sfx4) /\
   prefill_read_aux C1 ssfx4 acc offsets  = [(assign_public off10 load10)] /\
   prefill_read_aux_ntr C1 ssfx4 offsets  = [(assign_public off10 load10)]) /\
  (well_bracketed_trace st4 (ret_ev2::sfx5) /\
   prefill_read_aux C2 ssfx5 acc offsets  =
   [(assign_public off14 load14) ; (assign_public off12 load12)] /\
   prefill_read_aux_ntr C2 ssfx5 offsets  =
   [(assign_public off12 load12) ; (assign_public off14 load14)]) /\
  (well_bracketed_trace st5 (ret_ev3::sfx6) /\
   prefill_read_aux C1 ssfx6 acc offsets  =
   [(assign_public off13 load13)] /\
   prefill_read_aux_ntr C1 ssfx6 offsets  =
   [(assign_public off13 load13)]).
Proof.
  (* well formed events sanity check *)
  simpl ; rewrite /imported_procedure_b ; simpl.
  split ; first by find_in_fset.
  done.
Qed.


(** Checking modified comp_subtrace *)
Example test_comp_subtrace0 :
  let '(C1,P1) := (1,1) in
  let '(arg1, ret1) := (17%Z, 42%Z) in
  let '(off1, load1, off2, load2) := (1%Z, Int 420%Z, 2%Z, Int 1337%Z) in
  let ev1 := ECall Component.main P1 arg1 C1 in
  let ev2 := ERet C1 ret1 Component.main in
  let ev3 := ELoad Component.main off1 load1 C1 in
  let ev4 := ELoad Component.main off2 load2 C1 in
  comp_subtrace Component.main [ ev1; ev2; ev3 ; ev4 ] = [ev1 ; ev3 ; ev4].
Proof.
  simpl. reflexivity. Qed.

Example test_comp_subtrace1 :
  let '(C1,P1) := (1,1) in
  let '(arg1, ret1) := (17%Z, 42%Z) in
  let '(off1, load1, off2, load2) := (1%Z, Int 420%Z, 2%Z, Int 1337%Z) in
  let ev1 := ECall Component.main P1 arg1 C1 in
  let ev2 := ERet C1 ret1 Component.main in
  let ev3 := ELoad Component.main off1 load1 C1 in
  let ev4 := ELoad Component.main off2 load2 C1 in
  comp_subtrace C1 [ ev1; ev2; ev3 ; ev4 ] = [ev2 ; ev3 ; ev4].
Proof.
  simpl. reflexivity. Qed.

(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CompCert.Events.

Require Import Common.Definitions.
Require Import Common.Maps.

Require Import I2SFI.Compiler.
Require Import TargetSFI.Machine.
Require Import TargetSFI.EitherMonad.
Require Import TargetSFI.StateMonad.
Require Import TargetSFI.CS.
Require Import TargetSFI.SFIUtil.
Require Import CompEitherMonad.
Require Import CompStateMonad.
Require Import TestIntermediate.

Require Import Intermediate.Machine.
Require Import Intermediate.CS.

Require Import CompTestUtil.
Require Import I2SFI.Shrinkers.
Require Import TargetSFI.SFITestUtil.
Require Import I2SFI.IntermediateProgramGeneration.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import CoqUtils.ord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DoNotation.
Import ssrfun.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.
Import DoNotation.

Definition get_freq_store i :=
  match i with
  | Nop => 1%nat
  | Label => 4%nat
  | Const => 4%nat
  | Mov => 2%nat
  | BinOp => 6%nat
  | Load => 4%nat
  | Store => 0%nat
  | Alloc => 4%nat
  | Bnz => 1%nat (* could generate infinite loops *)
  | Jump => 1%nat
  | Jal => 1%nat
  | Call => 4%nat
  | Return => 2%nat
  | Halt => 1%nat
  end.

Inductive checker_type : Type :=
| CStore : checker_type
| CJump : checker_type
| CStack : checker_type.

Definition get_freq_jump i :=
  match i with
  | Nop => 1%nat
  | Label => 4%nat
  | Const => 4%nat
  | Mov => 2%nat
  | BinOp => 6%nat
  | Load => 4%nat
  | Store => 4%nat
  | Alloc => 4%nat
  | Bnz => 1%nat (* could generate infinite loops *)
  | Jump => 20%nat
  | Jal => 1%nat
  | Call => 4%nat
  | Return => 2%nat
  | Halt => 1%nat
  end.

Definition get_freq_call i :=
  match i with
  | Nop => 1%nat
  | Label => 4%nat
  | Const => 4%nat
  | Mov => 2%nat
  | BinOp => 6%nat
  | Load => 4%nat
  | Store => 40%nat
  | Alloc => 4%nat
  | Bnz => 1%nat (* could generate infinite loops *)
  | Jump => 40%nat
  | Jal => 1%nat
  | Call => 40%nat
  | Return => 2%nat
  | Halt => 1%nat
  end.

Definition get_weigths (ct : checker_type) : instr_weight :=
  match ct with
  | CStore => get_freq_store
  | CJump => get_freq_jump
  | CStack => get_freq_call
  end.


Definition gen_code_address_offset : G N :=
  freq [ (8%nat, choose_N (0%N, 15%N));
           (8%nat, elems
                   [ (2*16+8)%N
                     ; (3*16+8)%N
                     ; (4*16+8)%N
                     ; (5*16+8)%N
                     ; (6*16+8)%N
                     ; (7*16+8)%N
                     ; (8*16+8)%N
                     ; (9*16+8)%N
                     ; (10*16+8)%N
                     ; (11*16+8)%N
                     ; (12*16+8)%N
                     ; (13*16+8)%N
                     ; (14*16+8)%N] ) ;
           ( 2%nat,
             (
               do! k <- elems [1%N; 2%N; 3%N; 4%N; 5%N; 6%N; 7%N; 8%N; 9%N ];
                 do! l <- elems [0%N; 1%N; 2%N; 3%N; 4%N; 5%N; 6%N; 7%N;
                                  8%N; 9%N; 10%N; 11%N; 12%N; 13%N; 14%N; 15%N ];
                 returnGen (16*k+l)%N                   
             )
           )
       ].

Definition genIConstCodeAddress
           (ct : checker_type)
           (r : Intermediate.Machine.register)
           (pi : prog_int)
           (cid : Component_id)
  : G (list instr) :=
  match ct with
  | CJump =>
    do! cid' <- choose_N (1%N, (SFI.COMP_MAX - 1)%N);
      do! cid1 <- elems [0%N;cid'];
      do! pid <- choose_N (1%N, (N.of_nat MAX_PROC_PER_COMP));
      do! offset <- (
          do! k <- elems [1%N; 2%N; 3%N ];
            do! l <- elems [0%N; 1%N; 2%N; 3%N; 4%N; 5%N; 6%N; 7%N;
                             8%N; 9%N; 10%N; 11%N; 12%N; 13%N; 14%N; 15%N ];
            returnGen (16*k+l)%N                   
        );
      let v := SFI.address_of
                 cid1
                 (2*(pid - 1))%N
                 offset in
      returnGen ([IConst (IInt (Z.of_N v)) r])
  | _ =>
    do! pid <-
      ( match BinNatMap.find cid pi with
        | None => returnGen 1%nat
        | Some (exp,_) => choose (0%nat,((List.length exp) - 1)%nat)
        end);
      do! offset <-  gen_code_address_offset;
      let v := SFI.address_of
                 cid
                 (2*(N.of_nat pid))%N
                 offset in
      returnGen ([IConst (IInt (Z.of_N v)) r])
  end.

Definition pos_of_N (n : N) :=
    match n with
    | N0 => 1%positive
    | Npos p => p
    end.

Definition genTargetedStore
           (ct : checker_type)
           (r1 r2: Intermediate.Machine.register)
           (pi : prog_int)
           (buffers : BinNatMap.t (list (Block_id * (nat+list value))))
           (cid : Component_id)
    : G (list instr) :=

      (* 50% in component zero *)
      do! cid' <- choose_N (1%N, (SFI.COMP_MAX - 1)%N);
      do! cid1 <- elems [0%N;cid'];

      (* (* valid slot id *) *)
      do! bid <-
        match ct with
        | CStack =>
          freq [ (1%nat,returnGen 0%N);
                   (1%nat, choose_N (1%N,3%N)) ]
        | _ => 
          (match BinNatMap.find cid' buffers with
           | None => 
             choose_N (0%N, ((N.of_nat MAX_NO_BUFFERS_PER_COMP)-1)%N)
           | Some lst => choose_N (1%N, N.of_nat (List.length lst) )
           end)
        end;

      do! offset' <- choose_N (1%N, N.of_nat MAX_BUFFER_SIZE);
      do! offset <-
        match ct with
        | CStack => returnGen 0%N
        | _ => elems [0%N;offset']
        end;

      let v := SFI.address_of cid1
                              (2*bid+1)%N
                              offset in
      do! li <- genIConstCodeAddress ct r2 pi cid;
      
      returnGen  (li ++ [IConst (IInt (Z.of_N v)) r1])%list.

Definition genStoreAddresConstInstr
           (ct : checker_type)
           (r1 r2: Intermediate.Machine.register)
           (pi : prog_int)
           (buffers : BinNatMap.t (list (Block_id * (nat+list value))))
           (cid : Component_id)
    : G (list instr) :=
  match ct with
  | CStore
  | CStack
    => genTargetedStore ct r1 r2 pi buffers cid
  | _ =>
    do! res <- genPtrImVal pi buffers cid true;
      match res with
    | None => returnGen []
    | Some ptr =>
      returnGen [IConst ptr r1]
    end
  end.


  (* Definition genPointer (cid : N) *)
  (*            (buffers : BinNatMap.t (list (N * (nat+list value)))) := *)
  (*   let nat_cid := N.to_nat cid in *)
  (*   match BinNatMap.find cid buffers with *)
  (*   | None => returnGen None *)
  (*   | Some lst => *)
  (*     match lst with *)
  (*     | nil => returnGen None *)
  (*     | b::xs => *)
  (*       do! b' <- elements b xs; *)
  (*         let '(bid,bs) := b in *)
  (*         let nat_bid := N.to_nat bid in *)
  (*         match bs with *)
  (*         | inl sz => *)
  (*           if Nat.eqb sz 0%nat *)
  (*           then returnGen None *)
  (*           else *)
  (*             if Nat.eqb sz 1%nat *)
  (*             then *)
  (*               returnGen *)
  (*                 (Some (Intermediate.Machine.IPtr *)
  (*                          ((nat_cid, nat_bid), 0%Z))) *)
  (*             else *)
  (*               let up := (sz-1)%nat in *)
  (*               do! offset <- choose (0%nat, up); *)
  (*                 returnGen (Some (Intermediate.Machine.IPtr *)
  (*                                    ((nat_cid, nat_bid), Z.of_nat offset))) *)
  (*         | inr lst => *)
  (*           if (Nat.eqb (List.length lst) 1%nat) *)
  (*           then *)
  (*             returnGen (Some (Intermediate.Machine.IPtr *)
  (*                                ((nat_cid, nat_bid), Z0) )) *)
  (*           else *)
  (*             do! offset <- choose (0%nat,((List.length lst) - 1)%nat); *)
  (*             returnGen (Some (Intermediate.Machine.IPtr *)
  (*                                ((nat_cid, nat_bid), Z.of_nat offset))) *)
  (*         end *)
  (*     end *)
  (*   end. *)

(*   Definition gen_procedures *)
(*              (t : test_type) *)
(*              (pi : prog_int) *)
(*              (buffers : BinNatMap.t (list (N * (nat+list value)))) *)
(*     : G (BinNatMap.t (BinNatMap.t Intermediate.Machine.code)) := *)

(*    foldGen *)
(*      (fun acc '(cid, comp_interface)  => *)
(*         do! proc_map <- ( *)
(*             let '(lexp,limp) := comp_interface in *)
(*             foldGen *)
(*               (fun acc pid => *)
(*                  do! proc <- gen_procedure t  pi buffers cid pid ((max_label acc) + 1)%nat; *)
(*                         returnGen (BinNatMap.add pid proc acc) *)
(*               ) lexp (BinNatMap.empty Intermediate.Machine.code)); *)

(*           (* check add labels as needed for IJal *) *)
(*           let all_decl_labels := List.fold_left *)
(*                                    (fun acc elt => (acc ++ elt)%list ) *)
(*                                    (List.map (fun p => delared_labels_in_proc (snd p)) *)
(*                                              (BinNatMap.elements proc_map)) *)
(*                                    (@nil nat) in *)
(*           let uses := List.fold_left *)
(*                         (fun acc elt => (acc ++ elt)%list ) *)
(*                         (List.map (fun p => *)
(*                                      List.map (fun i => *)
(*                                                  match i with *)
(*                                                  | IJal l => l *)
(*                                                  | _ => 1%nat (* this is not happening *) *)
(*                                                  end *)
(*                                               ) *)
(*                                               (List.filter (fun i => match i with *)
(*                                                                   | IJal _  => true *)
(*                                                                   | _ => false *)
(*                                                                   end ) *)
(*                                                            (snd p) )) *)
(*                                   (BinNatMap.elements proc_map)) *)
(*                         (@nil nat) in *)
(*           let lbls := List.nodup label_eq_dec *)
(*                                  (List.filter (fun l => *)
(*                                                  Nat.eqb 0%nat *)
(*                                                          (List.count_occ *)
(*                                                             label_eq_dec *)
(*                                                             all_decl_labels *)
(*                                                             l *)
(*                                                          ) *)
(*                                               ) *)
(*                                               uses *)
(*                                  ) in *)
(*           (* TODO do something smarter *) *)
(*           match BinNatMap.elements proc_map with *)
(*           | nil => returnGen (BinNatMap.add cid proc_map acc) *)
(*           | (pid,code)::_ => returnGen (BinNatMap.add cid *)
(*                                                   (BinNatMap.add *)
(*                                                      pid *)
(*                                                      ( *)
(*                                                        ( *)
(*                                                          List.map *)
(*                                                            (fun l => ILabel l) *)
(*                                                            lbls *)
(*                                                        )++code *)
(*                                                      )%list *)
(*                                                      proc_map *)
(*                                                   ) *)
(*                                                   acc *)
(*                                       ) *)
(*           end *)
(*           ) (BinNatMap.elements  pi) *)
(*           (BinNatMap.empty (BinNatMap.t Intermediate.Machine.code)) *)
(* . *)

(**************************
 * Log data structures
 **************************)

Definition log_type (entry_type : Type) :=
  ((list entry_type) * (list RiscMachine.address))%type.


(**************************
 * Log Update Functions 
 **************************)

Definition update_records {entry_type:Type} := 
  Env.t ->
  MachineState.t -> CompCert.Events.trace ->
  MachineState.t -> (log_type entry_type) -> (log_type entry_type).


(************************************************
 * Checkers
 ************************************************)
Definition log_checker  {entry_type:Type} :=
  (log_type entry_type ) -> nat -> MachineState.t -> Checker.

(*****************************************************
 * Checkers when target execution returnd error
 ******************************************************)

Definition log_checker_error {entry_type:Type} :=
  (log_type entry_type) -> TargetSFI.EitherMonad.ExecutionError -> Checker.


Definition eval_program {X:Type} (update_fun : update_records) (ct : checker_type) (p : sfi_program) (fuel : nat)
  : (@Either (CompCert.Events.trace*MachineState.t*nat) * (log_type X) ) :=
  ((CS.eval_program_with_state     
     (log_type X)
     update_fun
     fuel
     p
     (RiscMachine.RegisterFile.reset_all)) (nil,nil)).


Definition check_correct {log_entry_type : Type}
           (t : instr_gen)
           (ct : checker_type)
           (update_fun : update_records)
           (log_checker_error_fun : log_checker_error)
           (log_checker_fun : log_checker)
           (fuel : nat)
  : Checker :=
  forAllShrink
    (genIntermediateProgram
       t
       (match ct with
        | CStore => get_freq_store
        | CJump => get_freq_jump
        | CStack => get_freq_call
        end)
       (genIConstCodeAddress ct)
       (genStoreAddresConstInstr ct)
    ) shrink
    ( fun ip =>
        match compile_program ip with
        | CompEitherMonad.Left msg err =>
          whenFail ("Compilation error: " ++ msg ++ newline ++ (show err) ) false
        | CompEitherMonad.Right p =>
          let '(res,log) := @eval_program log_entry_type update_fun ct p fuel in
          match res with
          | TargetSFI.EitherMonad.Left msg err =>
            log_checker_error_fun log err
          | TargetSFI.EitherMonad.Right (t, st,steps) => 
            (whenFail ("memory of failed program: " ++ (show_mem (MachineState.getMemory st)))%string
                      (log_checker_fun log steps st))
          end
        end).

(* Definition FUEL := 100%nat. *)

(* Definition run_intermediate_program (ip : Intermediate.program) := *)
(*   runp FUEL ip. *)

(* (************************************************ *)
(*  * No writes outside its own memory, *)
(*  * except for push sfi. *)
(*  *************************************************) *)

(* Definition store_log_entry := (RiscMachine.pc * RiscMachine.address * RiscMachine.value)%type. *)

(* Definition store_log := ((list store_log_entry) * (list RiscMachine.address))%type. *)

(* Definition update_store_log *)
(*            (G : Env.t) *)
(*            (st : MachineState.t) (t : CompCert.Events.trace) *)
(*            (st' : MachineState.t) (log : store_log) := *)
(*   let '(mem,pc,regs) := st in *)
(*   let '(st_log,addr_log) := log in *)
(*   let nlog := *)
(*       if (Nat.eqb (List.count_occ N.eq_dec addr_log pc) 0%nat) *)
(*       then (addr_log ++ [pc])%list *)
(*       else addr_log *)
(*   in *)
(*   match RiscMachine.Memory.get_word mem pc with *)
(*   | Some (RiscMachine.Instruction instr) => *)
(*     match instr with *)
(*     | RiscMachine.ISA.IStore rptr rs => *)
(*       match RiscMachine.RegisterFile.get_register rptr regs with *)
(*       | Some ptr => *)
(*         let addr := RiscMachine.Memory.to_address ptr in *)
(*         match RiscMachine.RegisterFile.get_register RiscMachine.Register.R_SFI_SP regs with *)
(*         | Some sp => ((st_log ++ [(pc,addr,sp)])%list,nlog) *)
(*         | _ => (st_log,nlog) *)
(*         end *)
(*       | _ => (st_log,nlog) *)
(*       end *)
(*     | _ => (st_log,nlog) *)
(*     end *)
(*   | _ => (st_log,nlog) *)
(*   end. *)

(* Definition show_log_entry (entry : store_log_entry) : string := *)
(*   let '(pc,addr,sfi_sp) := entry in *)
(*    "pc: " ++ (show_addr pc) *)
(*           ++ " ptr: " *)
(*           ++ (show_addr addr) *)
(*           ++ " sfi sp: " ++ (show sfi_sp). *)


(* (* 1. number of instr exec, *)
(*    2. number of internal writes, *)
(*    3. number of push sfi, *)
(*    4. result of intermediate program *)
(*    5. number of static instructions executed *)
(* *) *)
(* Definition store_stat := (nat * nat * nat *)
(*                           * (@execution_state (CompCert.Events.trace*CS.state)) * nat)%type. *)

(* Instance show_store_stat : Show store_stat := *)
(*   {| *)
(*     show := *)
(*       fun ss => *)
(*         let '(steps, i, e, es, si) := ss in *)
(*          "Steps: " *)
(*            ++ (show  steps) *)
(*            ++ " Internal: " *)
(*            ++ (show i ) *)
(*            ++ " Push SFI: " *)
(*            ++ (show e) *)
(*            ++ " Intermediate Execution: " *)
(*            ++ (show es) *)
(*            ++ " Static instructions: " *)
(*            ++ (show si) *)
(*   |}. *)

(* Definition store_stats (log : store_log) (steps : nat) *)
(*            (es : (@execution_state (CompCert.Events.trace*CS.state))) : store_stat := *)
(*   let '(l1,l2) := log in *)
(*   let i := (List.length (List.filter (fun '(pc,addr,sfi_sp) => *)
(*                                         (SFI.is_same_component_bool pc addr) *)
(*                                      ) l1 *)
(*                         ) *)
(*            ) in *)
(*   ( steps, i, ((List.length l1) - i)%nat, es, List.length l2). *)


(* Definition eval_store_program (p : sfi_program) *)
(*   : (@Either (CompCert.Events.trace*MachineState.t*nat) * store_log ) := *)
(*   ((CS.eval_program_with_state *)
(*      store_log *)
(*      update_store_log *)
(*      FUEL *)
(*      p *)
(*      (RiscMachine.RegisterFile.reset_all)) (nil,nil)). *)

(* Definition store_checker (log : store_log) (steps : nat) *)
(*            (es : (@execution_state (CompCert.Events.trace*CS.state))): Checker := *)
(*   let (l1,l2) := log in *)
(*   collect *)
(*     (store_stats log steps es) *)
(*     match l1 with *)
(*     | nil => checker tt *)
(*     | _ => *)
(*       conjoin (List.map (fun '(pc,addr,sfi_sp) => *)
(*                            if (SFI.is_same_component_bool pc addr) *)
(*                            then checker true *)
(*                            else *)
(*                              if (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID) *)
(*                              then *)
(*                                whenFail ("Failed at: " *)
(*                                            ++ (show_log_entry (pc,addr,sfi_sp)) )%string *)
(*                                         (N.eqb addr (SFI.address_of *)
(*                                                        SFI.MONITOR_COMPONENT_ID *)
(*                                                        (Z.to_N (2 * sfi_sp +1)) *)
(*                                                        0)) *)
(*                              else *)
(*                                whenFail ("Failed at: " *)
(*                                            ++ (show_log_entry (pc,addr,sfi_sp)) )%string *)
(*                                         false *)
(*                         ) l1) *)
(*     end. *)

(* Definition store_correct  (t : test_type) : Checker := *)
(*   (* forAllShrink (genIntermediateProgram t) shrink *) *)
(*     forAll (genIntermediateProgram t)  *)
(*   ( fun ip => *)
(*       match compile_program ip with *)
(*       | CompEitherMonad.Left msg err => *)
(*         whenFail ("Compilation error: " ++ msg ++ newline ++ (show err) ++ newline ++ (show ip) ) false *)
(*       | CompEitherMonad.Right p => *)
(*         let '(res,log) := eval_store_program p in *)
(*         let es := run_intermediate_program ip in *)
(*         match es with *)
(*         | Wrong _ msg InvalidEnv *)
(*         | Wrong _ msg (NegativePointerOffset _) *)
(*         | Wrong _ msg MissingJalLabel *)
(*         | Wrong _ msg MissingLabel *)
(*         | Wrong _ msg (MissingBlock _) *)
(*         | Wrong _ msg (OffsetTooBig _) *)
(*         | Wrong _ msg (MemoryError _ _) *)
(*         | Wrong _ msg AllocNegativeBlockSize *)
(*         | Wrong _ msg NoInfo *)
(*         | Wrong _ msg (MissingComponentId _) => *)
(*           if DEBUG *)
(*           then *)
(*             whenFail ((show es) ++ (show ip))%string false *)
(*           else *)
(*             checker tt *)
(*         | _ => *)
(*           match res with *)
(*           | TargetSFI.EitherMonad.Left msg err => whenFail *)
(*                                                    (msg ++ (show err)) *)
(*                                                    (store_checker log 0%nat es) *)
(*           | TargetSFI.EitherMonad.Right (t,(mem,_,regs),steps) => *)
(*             (whenFail ("memory of failed program: " ++ (show_mem  mem))%string *)
(*                       (store_checker log steps es)) *)
(*           end *)
(*         end *)
(*       end *)
(*   ). *)

(* (******************************************** *)
(*  * Jumps *)
(*  ************************************************) *)

(* Inductive jump_type := *)
(* | Indirect : RiscMachine.Register.t -> jump_type *)
(* | Direct : jump_type *)
(* . *)

(* Instance show_jump_type : Show jump_type := *)
(*   {| *)
(*     show := *)
(*       fun t => *)
(*         match t with *)
(*         | Indirect r => "Jmp " ++ (show r) *)
(*         | Direct => "Jal" *)
(*         end *)
(*   |}. *)

(* Definition jump_log_entry := (RiscMachine.pc * RiscMachine.address *)
(*                              * jump_type * CompCert.Events.trace)%type. *)

(* Definition jump_log := ((list jump_log_entry) * (list RiscMachine.address))%type. *)

(* Definition update_jump_log *)
(*            (G : Env.t) *)
(*            (st : MachineState.t) (t : CompCert.Events.trace) *)
(*            (st' : MachineState.t) (log : jump_log) := *)
(*   let '(mem,pc,regs) := st in *)
(*   let '(j_log,addr_log) := log in *)
(*   let nlog := *)
(*       if (Nat.eqb (List.count_occ N.eq_dec addr_log pc) 0%nat) *)
(*       then (addr_log ++ [pc])%list *)
(*       else addr_log *)
(*   in *)
(*   match RiscMachine.Memory.get_word mem pc with *)
(*   | Some (RiscMachine.Instruction instr) => *)
(*     match instr with *)
(*     | RiscMachine.ISA.IJump r  => *)
(*       if (N.eqb r RiscMachine.Register.R_RA) || (N.eqb r RiscMachine.Register.R_T) *)
(*       then *)
(*         match RiscMachine.RegisterFile.get_register r regs with *)
(*         | Some ptr => ((j_log ++ [(pc, RiscMachine.Memory.to_address ptr,Indirect r,t)])%list,nlog) *)
(*         | _ => (j_log,nlog) *)
(*         end *)
(*       else (j_log,nlog) *)
(*     | RiscMachine.ISA.IJal addr => ((j_log ++ [(pc,addr,Direct,t)])%list,nlog) *)
(*     | _ => (j_log,nlog) *)
(*     end *)
(*   | _ => (j_log,nlog) *)
(*   end. *)

(* Definition show_jump_log_entry (entry : jump_log_entry) : string := *)
(*   let '(pc,addr,type,t) := entry in *)
(*    "pc: " ++ (show pc) *)
(*           ++ " ptr: " *)
(*           ++ (show addr) *)
(*           ++ " type: " *)
(*           ++ ( match type with *)
(*                | Indirect r => "Jmp " ++ (show r) *)
(*                | Direct => "Jal" *)
(*                end) *)
(*           ++ " trace: " ++ (show t). *)

(* Definition eval_jump_program (p : sfi_program) *)
(*   : (@Either (CompCert.Events.trace*MachineState.t*nat) * jump_log) := *)
(*   ((CS.eval_program_with_state *)
(*      jump_log *)
(*      update_jump_log *)
(*      FUEL *)
(*      p *)
(*      (RiscMachine.RegisterFile.reset_all)) (nil,nil)). *)

(* (* 1. number of instr exec, *)
(*    2. number of internal jumps, *)
(*    3. number of cross component jumps *)
(*    4. result of intermediate program *)
(*    5. number of static instructions executed *)
(* *) *)
(* Definition jump_stat := (nat * nat * nat *)
(*                          * (@execution_state (CompCert.Events.trace*CS.state)) * nat)%type. *)

(* Instance show_jump_stat : Show jump_stat := *)
(*   {| *)
(*     show := *)
(*       fun ss => *)
(*         let '(steps, i, e, es,si) := ss in *)
(*          "Steps: " *)
(*            ++ (show  steps) *)
(*            ++ " Internal: " *)
(*            ++ (show i ) *)
(*            ++ " Cross Component: " *)
(*            ++ (show e) *)
(*            ++ " Intermediate Execution: " *)
(*            ++ (show es) *)
(*            ++ " Static instructions: " *)
(*            ++ (show si) *)
(*   |}. *)

(* Definition jump_stats (log : jump_log) (steps : nat) *)
(*            (es : (@execution_state (CompCert.Events.trace*CS.state))) : jump_stat := *)
(*   let '(l1,l2) := log in *)
(*   let i := (List.length *)
(*               (List.filter *)
(*                  (fun '(pc,addr,type,t) => *)
(*                     (SFI.is_same_component_bool pc addr) *)
(*                     || (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID) *)
(*                     || (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID) *)
(*                  ) l1 *)
(*               ) *)
(*            ) in *)
(*   let e := (List.length *)
(*               (List.filter *)
(*                  (fun  '(pc,addr,type,t) => *)
(*                     negb ( *)
(*                         (SFI.is_same_component_bool pc addr) *)
(*                         || (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID) *)
(*                         || (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID) *)
(*                       ) *)
(*                  ) l1 *)
(*               ) *)
(*            ) in *)
(*   ((steps,i), e,es,List.length l2). *)

(* Definition jump_checker (log : jump_log) (steps : nat) *)
(*            (es : (@execution_state (CompCert.Events.trace*CS.state))) : Checker := *)
(*   let (l1,l2) := log in *)
(*    collect *)
(*      (jump_stats log steps es) *)
(*       match l1 with *)
(*       | nil => checker tt *)
(*       | _ => *)
(*         conjoin ( *)
(*             List.map *)
(*               (fun '(pc,addr,type,t) => *)
(*                  if (N.eqb (SFI.C_SFI addr) SFI.MONITOR_COMPONENT_ID) *)
(*                  then checker true *)
(*                  else *)
(*                    if (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID) *)
(*                    then checker true *)
(*                    else *)
(*                      if (SFI.is_same_component_bool pc addr) *)
(*                      then *)
(*                        match t with *)
(*                        | nil =>  whenFail ("Register R_T expected in internal jumps " *)
(*                                             ++ (show type)) *)
(*                                          (match type with *)
(*                                           | Indirect r => RiscMachine.Register.eqb *)
(*                                                            RiscMachine.Register.R_T r *)
(*                                           | Direct => true *)
(*                                           end) *)
(*                        | _ => whenFail ("Unexpectected event at log entry:" *)
(*                                          ++ (show_jump_log_entry (pc,addr,type,t))) *)
(*                                       false *)
(*                        end *)
(*                      else *)
(*                          match t with *)
(*                          | _::_ =>  whenFail ("Register R_A expected in internal jumps " *)
(*                                                ++ (show type)) *)
(*                                             (match type with *)
(*                                              | Indirect r => RiscMachine.Register.eqb *)
(*                                                               RiscMachine.Register.R_RA r *)
(*                                              | Direct => true *)
(*                                              end) *)
(*                          | nill => whenFail ("Unexpectected empty event at log entry:" *)
(*                                               ++ (show_jump_log_entry (pc,addr,type,t))) *)
(*                                            false *)
(*                          end *)
(*               ) l1) *)
(*       end. *)

(* Definition jump_correct  (t : test_type) : Checker := *)
(*   (* forAllShrink (genIntermediateProgram TJump) shrink *) *)
(*   forAll (genIntermediateProgram TJump)  *)
(*          ( fun ip => *)
(*              match compile_program ip with *)
(*              | CompEitherMonad.Left msg err => *)
(*                whenFail ("Compilation error: " ++ msg ++ newline *)
(*                                                ++ (show err) ++ newline ++ (show ip) ) false *)
(*              | CompEitherMonad.Right p => *)
(*                let (res,log) := eval_jump_program p in *)
(*                let es := run_intermediate_program ip in *)
(*                match es with *)
(*                | Wrong _ msg InvalidEnv *)
(*                | Wrong _ msg (NegativePointerOffset _) *)
(*                | Wrong _ msg MissingJalLabel *)
(*                | Wrong _ msg MissingLabel *)
(*                | Wrong _ msg (MissingBlock _) *)
(*                | Wrong _ msg (OffsetTooBig _) *)
(*                | Wrong _ msg (MemoryError _ _) *)
(*                | Wrong _ msg (StoreMemoryError _ _) *)
(*                | Wrong _ msg AllocNegativeBlockSize *)
(*                | Wrong _ msg NoInfo *)
(*                | Wrong _ msg (MissingComponentId _) => *)
(*                  if DEBUG *)
(*                  then *)
(*                    whenFail ((show es) ++ (show ip))%string false *)
(*                  else *)
(*                    checker tt *)
(*                | _ => *)
(*                  match res with *)
(*                  | TargetSFI.EitherMonad.Left msg err => whenFail *)
(*                                                           (msg ++ (show err)) *)
(*                                                           (jump_checker log 0%nat es) *)
(*                  | TargetSFI.EitherMonad.Right (t,(mem,_,regs),steps) => *)
(*                    jump_checker log steps es *)
(*                  end *)
(*                end *)
(*              end *)
(*          ). *)


(* (******************************************************* *)
(*  * Control Stack *)
(*  **********************************************************) *)
(* Inductive stack_op := Push *)
(*                     | Pop. *)

(* Definition show_op op := *)
(*   match op with *)
(*   | Push => "Push" *)
(*   | Pop => "Pop" *)
(*   end. *)

(* Definition cs_log_entry := (RiscMachine.pc *)
(*                            * RiscMachine.address *)
(*                            * stack_op * RiscMachine.ISA.instr)%type. *)

(* Definition cs_log := ((list cs_log_entry) * (list RiscMachine.address))%type. *)

(* Definition update_cs_log *)
(*            (G : Env.t) *)
(*            (st : MachineState.t) (t : CompCert.Events.trace) *)
(*            (st' : MachineState.t) (log : cs_log) := *)
(*   let '(mem,pc,regs) := st in *)
(*   let '(cs_log,addr_log) := log in *)
(*   let nlog := *)
(*       if (Nat.eqb (List.count_occ N.eq_dec addr_log pc) 0%nat) *)
(*       then (addr_log ++ [pc])%list *)
(*       else addr_log *)
(*   in *)
(*   match RiscMachine.Memory.get_word mem pc with *)
(*   | Some (RiscMachine.Instruction instr) => *)
(*     match instr with *)
(*     | RiscMachine.ISA.IJump r  => *)
(*         match RiscMachine.RegisterFile.get_register r regs with *)
(*         | Some ptr => let addr := RiscMachine.Memory.to_address ptr in *)
(*                      if SFI.is_same_component_bool pc addr *)
(*                      then (cs_log,nlog) *)
(*                      else (* cross-component return *) *)
(*                          ((cs_log ++ [(pc, addr, Pop, instr)])%list,nlog) *)
(*         | _ => (cs_log,nlog) *)
(*         end *)

(*     | RiscMachine.ISA.IJal addr => *)
(*       if SFI.is_same_component_bool pc addr *)
(*       then (cs_log,nlog) *)
(*       else *)
(*         let '(mem',pc',regs') := st' in *)
(*         match RiscMachine.RegisterFile.get_register RiscMachine.Register.R_RA regs' with *)
(*         | Some addr => ((cs_log *)
(*                           ++ *)
(*                           [(pc, RiscMachine.Memory.to_address addr,Push, instr)])%list *)
(*                        ,nlog) *)
(*         | _ => (cs_log,nlog) *)
(*         end *)
(*     | _ => (cs_log,nlog) *)
(*     end *)
(*   | _ => (cs_log,nlog) *)
(*   end. *)

(* Definition show_cs_log_entry (entry : cs_log_entry) : string := *)
(*   let '(pc,addr,t, instr) := entry in *)
(*    "pc: " ++ (show_addr pc) *)
(*           ++ " ptr: " *)
(*           ++ (show_addr addr) *)
(*           ++ " stack op: " ++ (show_op t) *)
(*           ++ "instr " ++ (show instr). *)

(* Definition eval_cs_program (p : sfi_program) *)
(*   : (@Either (CompCert.Events.trace*MachineState.t*nat) * cs_log) := *)
(*   ((CS.eval_program_with_state *)
(*      cs_log *)
(*      update_cs_log *)
(*      FUEL *)
(*      p *)
(*      (RiscMachine.RegisterFile.reset_all)) (nil,nil)). *)

(* (* 1. number of instr exec, *)
(*    2. number of internal jump, *)
(*    3. number of cross component jumps *)
(*    4. result of intermediate program *)
(*    5. number of static instructions executed *)
(* *) *)
(* Definition cs_stat := (nat * nat *)
(*                        * (@execution_state (CompCert.Events.trace*CS.state)) * nat)%type. *)

(* Instance show_cs_stat : Show cs_stat := *)
(*   {| *)
(*     show := *)
(*       fun ss => *)
(*         let '(steps, op, es, si) := ss in *)
(*          "Steps: " *)
(*            ++ (show  steps) *)
(*            ++ " Operations no: " *)
(*            ++ (show op ) *)
(*            ++ " Intermediate Execution: " *)
(*            ++ (show es) *)
(*            ++ " Intermediate Execution: " *)
(*            ++ (show es) *)
(*            ++ " Static instructions: " *)
(*            ++ (show si) *)
(*   |}. *)

(* Definition cs_stats (log : cs_log) (steps : nat) *)
(*            (es : (@execution_state (CompCert.Events.trace*CS.state))) : cs_stat := *)
(*   let '(l1,l2) := log in *)
(*   (steps, (List.length l1), es, List.length l2). *)

(* Definition cs_checker (log : cs_log)  (steps : nat) *)
(*            (es : (@execution_state (CompCert.Events.trace*CS.state))) : Checker := *)
(*   let (l1,l2) := log in *)
(*   let fix aux l s := *)
(*       match l with *)
(*       | nil => checker true *)
(*       |  (pc,addr,op,instr)::xs => *)
(*          match op with *)
(*          | Push => aux xs (addr::s) *)
(*          | Pop => *)
(*            match s with *)
(*            | nil => whenFail ("Attemting to pop from empty stack at address" *)
(*                                ++ (show pc))%string false *)
(*            | a::s' => if (N.eqb a addr) *)
(*                      then aux xs s' *)
(*                      else whenFail ("Attemting address on the stack: " *)
(*                                       ++ (show_addr a) *)
(*                                       ++ " address in register: " *)
(*                                       ++ (show_addr addr) *)
(*                                       ++ "at pc: " *)
(*                                       ++ (show_addr pc) *)
(*                                       ++ " instr: " *)
(*                                       ++ (show instr) *)
(*                                    )%string *)
(*                                    false *)
(*            end *)
(*         end *)
(*       end *)
(*   in *)

(*   collect *)
(*     (cs_stats log steps es) *)
(*     match steps with *)
(*     | O => checker false *)
(*     | _ => *)
(*       match l1 with *)
(*       | nil => checker tt *)
(*       | _ => aux l1 [] *)
(*       end *)
(*     end. *)

(* Definition cs_correct (t : test_type) : Checker := *)
(*   forAll (genIntermediateProgram t)  *)
(*          ( fun ip => *)
(*              match compile_program ip with *)
(*              | CompEitherMonad.Left msg err => *)
(*                whenFail ("Compilation error: " ++ msg ++ newline *)
(*                                                ++ (show err) ++ newline ++ (show ip) ) false *)
(*              | CompEitherMonad.Right p => *)
(*                let (res,log) := eval_cs_program p in *)
(*                let es := run_intermediate_program ip in *)
(*                 match es with *)
(*                 | Wrong _ msg InvalidEnv *)
(*                 | Wrong _ msg (NegativePointerOffset _) *)
(*                 | Wrong _ msg MissingJalLabel *)
(*                 | Wrong _ msg MissingLabel *)
(*                 | Wrong _ msg (MissingBlock _) *)
(*                 | Wrong _ msg (OffsetTooBig _) *)
(*                 | Wrong _ msg (MemoryError _ _) *)
(*                 | Wrong _ msg (StoreMemoryError _ _) *)
(*                 | Wrong _ msg AllocNegativeBlockSize *)
(*                 | Wrong _ msg NoInfo *)
(*                 | Wrong _ msg (MissingComponentId _) => *)
(*                   if DEBUG *)
(*                   then *)
(*                     whenFail ((show es) ++ (show ip))%string false *)
(*                   else *)
(*                     checker tt *)
(*                 | _ => *)
(*                   match res with *)
(*                   | TargetSFI.EitherMonad.Left msg err => whenFail *)
(*                                                            (msg ++ (show err)) *)
(*                                                            (cs_checker log 0%nat es) *)
(*                   | TargetSFI.EitherMonad.Right (t,(mem,_,regs),steps) => *)
(*                     (whenFail ("memory of failed program: " ++ (show_mem  mem))%string *)
(*                               (cs_checker log steps es)) *)
(*                   end *)
(*                end *)
(*              end *)
(*          ). *)

(* (****************** QUICK CHECKS ***************************) *)
(* Extract Constant Test.defNumTests => "100". *)

(* QuickChick (store_correct TStore). *)
(* QuickChick (jump_correct TJump). *)
(* QuickChick (cs_correct TStack). *)


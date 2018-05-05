(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.ZArith.

Require Import CompCert.Events.

Require Import Common.CoqMaps.
Require Import Common.Values.
Require Import Common.Either.

Require Import Intermediate.Machine.

Require Import I2SFI.Compiler.

Require Import TargetSFI.Machine.
Require Import TargetSFI.CS.
Require Import TargetSFI.ExecutionError.

Require Import Tests.CompilerPBTests.
Require Import Tests.IntermediateProgramGeneration.
Require Import Tests.I2SFI.I2SFICompUtil.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Module DoNotation.
  Import ssrfun.
  Notation "'do!' X <- A ; B" :=
    (bindGen A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.
Import DoNotation.

Inductive checker_type : Type :=
| CStore : checker_type
| CJump : checker_type
| CStack : checker_type.

(**************************
 * Log data structures
 **************************)
(* first list rescords event of interest to the test
   second list records the program counter of the executed instructions *)
Definition log_type (entry_type:Type) :=
  ((list entry_type) * (list RiscMachine.address))%type.


(**************************
 * Log Update Functions 
 **************************)
(* env, old state, trace, new state, old log
   Returns: updated log *)
Definition update_records {entry_type:Type} := 
  Env.t ->
  MachineState.t -> CompCert.Events.trace ->
  MachineState.t ->
  (log_type entry_type) ->
  (log_type entry_type).


Definition get_freq_store (i : instr_type) :=
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

Definition get_freq_jump (i : instr_type) :=
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

Definition get_freq_call (i : instr_type) :=
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
           (max_components : nat)
           (r : Intermediate.Machine.register)
           (pi : prog_int)
           (cid : Component_id)
  : G (list instr) :=
  match ct with
  | CJump =>
    do! cid' <- choose_N (1%N, ((N.of_nat max_components) - 1)%N);
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
      returnGen ((IConst (IInt (Z.of_N v)) r)::nil)
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
      returnGen ((IConst (IInt (Z.of_N v)) r)::nil)
  end.

Definition genTargetedStore
           (ct : checker_type)
           (max_components : nat)
           (r1 r2: Intermediate.Machine.register)
           (pi : prog_int)
           (buffers : BinNatMap.t (list (Block_id * (nat+list value))))
           (cid : Component_id)
    : G (list instr) :=

      (* 50% in component zero *)
      do! cid' <- choose_N (1%N, ((N.of_nat max_components) - 1)%N);
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
      do! li <- genIConstCodeAddress ct max_components r2 pi cid;
      
      returnGen  (li ++ (IConst (IInt (Z.of_N v)) r1)::nil)%list.

Definition genStoreAddresConstInstr
           (ct : checker_type)
           (max_components : nat)
           (r1 r2: Intermediate.Machine.register)
           (pi : prog_int)
           (buffers : BinNatMap.t (list (Block_id * (nat+list value))))
           (cid : Component_id)
    : G (list instr) :=
  match ct with
  | CStore
  | CStack
    => genTargetedStore ct max_components r1 r2 pi buffers cid
  | _ =>
    do! res <- genPtrImVal pi buffers cid true;
      match res with
      | None => returnGen nil
      | Some ptr =>
        returnGen ((IConst ptr r1)::nil)
      end
  end.


Definition eval_program {X:Type}
           (update_fun : update_records)
           (* (ct : checker_type) *)
           (p : sfi_program)
           (fuel : nat)
  : (@Either (CompCert.Events.trace*MachineState.t*nat)%type ExecutionError)
    * (log_type X)
  :=
  ((CS.eval_program_with_state     
     (log_type X)
     update_fun
     fuel
     p
     (RiscMachine.RegisterFile.reset_all)) (nil,nil)).

Definition sfi_check_correct {log_entry_type : Type}
           (t : undef_allowed)
           (ct : checker_type)
           (update_fun : @update_records                           
                           log_entry_type)
           (log_checker_error_fun : @log_checker_error
                                      (@log_type log_entry_type)
                                      ExecutionError
           )
           (log_checker_fun : @log_checker
                                (@log_type log_entry_type)
                                (* execution result *)
                                (CompCert.Events.trace * MachineState.t * nat)
           )
           (fuel : nat)
  : Checker :=
  (* if we have 0 components we have a silly case *)
  let max_components := ((N.to_nat SFI.COMP_MAX) - 1)%nat in
  check_correct
    t
    (match ct with
        | CStore => get_freq_store
        | CJump => get_freq_jump
        | CStack => get_freq_call
        end)
    (genIConstCodeAddress ct max_components)
    (genStoreAddresConstInstr ct max_components)
    3%nat
    3%nat
    log_checker_error_fun
    log_checker_fun
    compile_program
    (eval_program update_fun)
    fuel.


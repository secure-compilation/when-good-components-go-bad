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
           (update_fun : @update_records log_entry_type)
           (log_checker_error_fun : @log_checker_error log_entry_type)
           (log_checker_fun : @log_checker log_entry_type)
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
       false
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



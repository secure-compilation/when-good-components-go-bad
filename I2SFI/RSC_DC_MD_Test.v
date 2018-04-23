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
Require Import I2SFI.CompilerPBTests.


From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Definition log_entry := (RiscMachine.pc
                         * CompCert.Events.trace)%type.

Definition show_log_entry (entry : log_entry) : string :=
  let '(pc,events) := entry in
  ("pc: " ++ (show pc)
         ++ " trace: " ++ (show t))%string.

Definition update_log
           (G : Env.t)
           (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t) (log :(log_type log_entry)) :=
  let '(mem,pc,regs) := st in
  let '(test_log,addr_log) := log in
  let nlog :=
      if (Nat.eqb (List.count_occ N.eq_dec addr_log pc) 0%nat)
      then (addr_log ++ [pc])%list
      else addr_log
  in
  match t with
  | nil =>  (test_log,nlog)
  | _ => ((test_log ++ [(pc,t)])%list,nlog)
  end.

(* TODO decide on statistics *)

(* ip intermediate program
   ctx_id the component id that must be defined 
   tr the trace to match
Returns: None if the definition is not possible
         (Some new_ip) intermediate program with same components, 
                       except ctx_id. ip and new_ip have the same 
                       interface
 *)

Definition  get_interm_program
            (ip : Intermediate.program)
            (ctx_cid : Component.id)
            (tr : CompCert.Events.trace) : @option Intermediate.program :=
   let export :=
      List.map (fun ev =>
                  match ev with
                  | ECall _ pid _ _ => pid
                  | _ => 0%nat
                  end
               )
               (List.filter
                  (fun ev =>
                     match ev with
                     | ECall _ _ _ cid => (Nat.eqb cid ctx_cid)
                     | _ => false
                     end                                               
                  ) tr) in
  let import :=
      List.map (fun ev =>
                  match ev with
                      | ECall _ pid _ cid => (cid,pid)
                      | _ => (0%nat,0%nat)
                  end)
               (List.filter
                  (fun ev =>
                     match ev with
                     | ECall cid _ _ _ => (Nat.eqb cid ctx_cid)
                     | _ => false
                     end ) tr) in
  
  let ctx_int :=  Component.mkCompInterface (list2fset export)
                                           (list2fset import) in
  let prog_interface :=
      setm (Intermediate.prog_interface ip)
           ctx_cid
           ctx_int in

  let buffer_ids := if (Nat.eqb Component.main ctx_cid)
                    then
                      (match (Intermediate.prog_main ip) with
                      | None => Procedure.main
                      | Some pid => pid
                      end)::export
                    else  export in
  let prog_buffers :=
      setm (Intermediate.prog_buffers ip)
           ctx_cid
           (
             mkfmap (List.map (fun id => (id, inr [(Int 0%Z)])) buffer_ids)
           ) in
  
  None
.

Definition rsc_correct (fuel : nat) :=
  forAll
    (genIntermediateProgram
       TestSpecific
       get_freq_call (* CStack *)
       (genIConstCodeAddress CJump) (* TODO *)
       (genStoreAddresConstInstr CStore) (* TODO *)
    ) 
    ( fun ip =>
        (* compile intermediate *)
        match compile_program ip with
        | CompEitherMonad.Left msg err =>
          whenFail ("Compilation error: " ++ msg ++ newline ++ (show err) ) false
        | CompEitherMonad.Right p =>
          (* run target *)
          let '(res,log) :=
              ((CS.eval_program_with_state 
                  (log_type log_entry)
                  update_log
                  fuel
                  p
                  (RiscMachine.RegisterFile.reset_all)) (nil,nil)) in
          let '(test_log,addr_log) := log in
          (* obtain target trace t_t *)
          let t_t := (List.flat_map snd test_log) in
          let cids := List.flat_map
                        (fun e =>
                           match e with
                           | ECall c1 _ _ c2 => [c1;c2]
                           | ERet c1 _ c2 => [c1;c2]
                           end
                        )
                        t_t in
          match cids with
          | nil => checker tt (* discard tests with empty traces *)
          | fcid::_ =>
            (* select context component ctx_cid *)
            let ctx_cid := List.last cids fcid in
            (* generate c_s *)
            match get_interm_program ip ctx_cid t_t with
            | None => whenFail "Can not define source component" (checker false)
            | Some newip =>
              (* run in intermediate semantics *)
              let interm_res := runp fuel newip in
              match interm_res with
              | Wrong t_s cid _ _ => (* t_s <= t_t undef not in ctx_cid *) 
                checker ( (sublist t_s t_t) && (negb (cid =? ctx_cid)))
              | _ => (* t_t <= t_s *)
                let t_s := 
                    match interm_res with
                    | Wrong tr _ _ _ => tr
                    | OutOfFuel (tr,_) => tr
                    | Halted tr => tr
                    | Running (tr,_) => tr 
                    end in
                checker (sublist t_t t_s)
              end
            end
          end
        end).
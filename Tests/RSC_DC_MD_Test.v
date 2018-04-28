Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CompCert.Events.

Require Import Common.Definitions.
Require Import Common.Maps.

Require Import Common.Either.
Require Import CompStateMonad.
Require Import TestIntermediate.

Require Import Intermediate.Machine.
Require Import Intermediate.CS.

Require Import CompTestUtil.
Require Import Tests.Shrinkers.
Require Import Tests.IntermediateProgramGeneration.
Require Import Tests.CompilerPBTests.
Require Import Tests.TargetSFI.SFITestUtil.


Require Import CoqUtils.ord.
From mathcomp Require Import ssreflect ssrfun ssrbool ssreflect.eqtype.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.


Definition Log := CompCert.Events.trace.

Definition get_freq_instr i :=
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
  | Jump => 4%nat
  | Jal => 1%nat
  | Call => 80%nat
  | Return => 2%nat
  | Halt => 1%nat
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

Definition generate_procedure_code ctx_cid pid (pmap : NMap code) (fst_lbl:nat)
  : (code*nat)%type :=
  let calls_no := List.length (elementsm pmap) in
  let res :=
      List.fold_left
        (fun acc cn =>
            (acc ++ [ ILabel (fst_lbl+cn)
                     ;  IConst (IInt (Z.of_nat cn)) R_AUX2
                     ; IBinOp Minus R_AUX2 R_AUX1 R_AUX2
                     ; IBnz R_AUX2 (fst_lbl+cn+1)%nat]
                ++
                match (getm pmap cn) with
                | None => nil (* no code *)
                | Some calls => calls
                end
                ++
                [ IConst (IInt 1%Z) R_ONE
                  ; IBnz R_ONE (fst_lbl+calls_no+1)])%list
        )
        (List.seq 1 calls_no)
        ([
            IConst (IPtr (ctx_cid,pid,0%Z)) R_AUX1
            ; ILoad R_AUX1 R_AUX1
            ; IConst (IInt 1%Z) R_ONE
            ; IBinOp Add R_ONE R_AUX1 R_AUX2
            ; IConst (IPtr (ctx_cid,pid,0%Z)) R_ONE
            ; IStore R_ONE R_AUX2
            ; IConst (IInt 1%Z) R_ONE
          ]) in
  ((res ++ [ILabel (fst_lbl+calls_no+1)])%list, (fst_lbl+calls_no+2)%nat)
.

Definition generate_ctx_component ctx_id main_pid tr export: NMap code :=
  let acc : (list (nat*nat*nat*nat))*(NMap nat) * (NMap (NMap code)) := 
      if (Nat.eqb ctx_id Component.main)
      then ([(Component.main,Component.main,main_pid,1%nat)],
            (mkfmap [(main_pid,1%nat)]),
            emptym
           )
      else ([],emptym,emptym) in
  let '(_,_,cmap) :=
      List.fold_left
        (fun acc elt =>
           let '(call_stack,call_nos,cmap) := acc in
           match elt with
           | ECall caller_cid pid rcom callee_cid =>
             (* generate Call instruction if necessary *)
             let new_cmap :=
                 match call_stack with
                 | nil => cmap 
                 | (_,_,ppid,pcn)::xs =>
                   if (Nat.eqb caller_cid ctx_id)
                   then
                     let pmap := match getm cmap ppid with
                                 | None => emptym
                                 | Some x => x
                                 end in
                     setm cmap
                          ppid
                          (setm
                             pmap
                             pcn
                             ((match (getm pmap pcn) with
                               | None => nil
                               | Some x => x
                               end)++[ IConst (IInt rcom) R_COM
                                       ; ICall callee_cid pid])%list)
                   else cmap
                   end in
             (* push call on the call stack *)
             if (Nat.eqb ctx_id callee_cid)
             then
               (* retrieve highest call number *)
               let cn :=
                   match (getm call_nos pid) with
                   | None => 0%nat
                   | Some n => n
                   end
               in
               let new_call_nos := (setm call_nos pid (cn+1)%nat) in               
               ((caller_cid,callee_cid,pid,(cn+1)%nat)::call_stack,
                new_call_nos, new_cmap)
             else
               (* not the context component, call number does not matter*)
               ((caller_cid,callee_cid,pid,1%nat)::call_stack,call_nos,new_cmap)
           | ERet crt_cid _ dst_cid =>
             match call_stack with
             | nil => acc (* TODO this is an error *)
             | (caller_id, callee_id, pid, _)::xs =>
               (xs, call_nos, cmap)
             end
           end
        )
        tr acc in
  let '(res,_) :=
      List.fold_left
        (fun '(acc,last_lbl) '(pid,pmap) =>
           let '(m,l) := (generate_procedure_code ctx_id pid pmap last_lbl) in
           (setm acc pid
                 (if (Nat.eqb ctx_id Component.main)
                       && (Nat.eqb pid main_pid)
                  then (m ++ [IHalt])%list
                  else (m ++ [IReturn])%list)
            , l)
        )
        (elementsm cmap)
        (emptym,0%nat) in
  List.fold_left
    (fun acc pid =>
       match getm acc pid with
       | Some _ => acc
       | None => setm acc pid [IReturn]
       end
    )
    export
    res.

Definition  get_interm_program
            (ip : Intermediate.program)
            (ctx_cid : Component.id)
            (tr : CompCert.Events.trace) : @option Intermediate.program :=
  match getm (Intermediate.prog_interface ip) ctx_cid with
  | None => None
  | Some ctx_interface =>
    let export := (val (Component.export ctx_interface)) in
    let import := (val (Component.import ctx_interface)) in
    
    let pid_main :=  (match (Intermediate.prog_main ip) with
                      | None => Procedure.main
                      | Some pid => pid
                      end) in

    let buffer_ids := if (Nat.eqb Component.main ctx_cid)
                      then pid_main::export
                      else export in
  let new_prog_buffers :=
      setm (Intermediate.prog_buffers ip)
           ctx_cid
           (mkfmap (List.map (fun id => (id, inr [(Int 1%Z)])) buffer_ids) ) in

  let new_prog_procedures :=
      setm (Intermediate.prog_procedures ip)
           ctx_cid
           (generate_ctx_component ctx_cid pid_main tr export) in
   Some {|
       Intermediate.prog_interface := (Intermediate.prog_interface ip);
       Intermediate.prog_procedures := new_prog_procedures;
       Intermediate.prog_buffers := new_prog_buffers;
       Intermediate.prog_main := Some pid_main
     |}
  end.

(* TODO *)
Definition rsc_correct
           {CompilerErrorType:Type}
           {TargetProgramType:Type}
           {ExecutionResult:Type} {ExecutionError:Type}
           `{Show CompilerErrorType}
           
           (cag : code_address_const_instr)
           (dag : data_address_const_instr)
           (max_components : nat)
           (cf : @compile TargetProgramType CompilerErrorType)
           (ef : @eval TargetProgramType ExecutionResult ExecutionError
                  Log
           )
           (fuel : nat) :=
  forAll
    (genIntermediateProgram
       TestSpecific
       get_freq_instr
       cag
       dag
       max_components
       true
    )
    ( fun ip =>
        (* compile intermediate *)
        match cf ip with
        | Common.Either.Left msg err =>
          whenFail ("Compilation error: " ++ msg ++ newline ++ (show err) ) false
        | Common.Either.Right p =>
          (* run target *)
          let '(res,log) :=  ef p fuel in
          (* obtain target trace t_t *)
          let t_t := log in
          let cids := List.flat_map
                        (fun e =>
                           match e with
                           | ECall c1 _ _ c2 => [c1;c2]
                           | ERet c1 _ c2 => [c1;c2]
                           end
                        )
                        t_t in
          match cids with
          | nil =>
            whenFail
                  ("Original program:"
                     ++ newline ++ (show ip) ++ newline
                     ++ "Target Trace: " ++ (show t_t) ++ newline )
                  (checker (*false*) tt ) (* discard tests with empty traces *)
          | fcid::_ =>
            (* select context component ctx_cid *)
            let ctx_cid := List.last cids fcid in
            (* generate c_s *)
            match get_interm_program ip ctx_cid t_t with
            | None => whenFail "Can not define source component" (checker false)
            | Some newip =>
              (* run in intermediate semantics *)
              let interm_res := runp (10*fuel)%nat newip in
              match interm_res with
              | Wrong t_s cid msg _ => (* t_s <= t_t undef not in ctx_cid *)
                whenFail
                  ("Original program:"
                     ++ newline ++ (show ip)
                     ++ "New Program: " ++ newline ++ (show newip)
                     ++ newline
                     ++ "Target Trace: " ++ (show t_t) ++ newline
                     ++ "Source Trace: " ++ (show t_s) ++ newline
                     ++ "Context component: " ++ (show ctx_cid) ++ newline
                     ++ "Execution error: " ++ msg
                  )
                  (checker
                     (
                       (sublist t_t t_s) ||
                       ((sublist t_s t_t) && (negb (cid =? ctx_cid)))
                     )
                  )
              | _ => (* t_t <= t_s *)
                let t_s :=
                    match interm_res with
                    | Wrong tr _ _ _ => tr
                    | OutOfFuel (tr,_) => tr
                    | Halted tr => tr
                    | Running (tr,_) => tr
                    end in
                whenFail
                  ("Original program:"
                     ++ newline ++ (show ip)
                     ++ "New Program: " ++ newline ++ (show newip)
                     ++ newline
                     ++ "Target Trace: " ++ (show t_t) ++ newline
                     ++ "Source Trace: " ++ (show t_s) ++ newline
                     ++ "Context component: " ++ (show ctx_cid) ++ newline
                     ++ "Source ended with: " ++
                     (match interm_res with
                     | Wrong _ _ _ _ => "Wrong"
                     | OutOfFuel _ => "OutOfFuel"
                     | Halted _ => "Halted"
                     | Running _ => "Running"
                     end) ++ newline
                  )
                   (checker
                     (
                       (sublist t_t t_s)
                       (*|| ((sublist t_s t_t) && (negb (cid =? ctx_cid)))*)
                     )
                  )
              end
            end
          end
        end).
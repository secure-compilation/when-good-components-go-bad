Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.
Require Import Coq.Strings.String.

Require Import CompCert.Events.
Require Import Common.Definitions.

Require Import I2SFI.CompilerPBTests.
Require Import I2SFI.CompTestUtil.
Require Import I2SFI.TestIntermediate.
Require Import I2SFI.Compiler.

Require Import TargetSFI.Machine.
Require Import TargetSFI.EitherMonad.
Require Import TargetSFI.CS.
Require Import TargetSFI.SFITestUtil.

Require Import Intermediate.CS.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Definition correct_log := (CompCert.Events.trace * (list RiscMachine.address))%type.

Definition update_correct_log
           (G : Env.t)
           (st : MachineState.t)
           (t : CompCert.Events.trace)
           (st' : MachineState.t)
           (log : correct_log) :=
  let '(mem,pc,regs) := st in
  let '(c_log,addr_log) := log in
  let nlog :=
      if (Nat.eqb (List.count_occ N.eq_dec addr_log pc) 0%nat)
      then (List.app addr_log (pc::nil))
      else addr_log
  in
  match RiscMachine.Memory.get_word mem pc with
  | Some (RiscMachine.Instruction instr) =>
    match instr with
    | RiscMachine.ISA.IJump reg =>
      match  RiscMachine.RegisterFile.get_register reg regs with
      | None => (c_log,nlog)
      | Some addr =>
        let pc' := RiscMachine.Memory.to_address addr in
        if SFI.is_same_component_bool pc pc' then
          (c_log,nlog)
        else
          if (N.eqb (SFI.C_SFI pc') SFI.MONITOR_COMPONENT_ID)
          then
            (c_log,nlog)
          else
            match RiscMachine.RegisterFile.get_register RiscMachine.Register.R_COM regs with
            | None => (c_log,nlog)
            | Some rcomval =>
              match (Env.get_component_name_from_id (SFI.C_SFI pc) G) with
              | None => (c_log,nlog)
              | Some cpc => 
                match (Env.get_component_name_from_id (SFI.C_SFI pc') G) with
                | None => (c_log,nlog)
                | Some cpc' =>
                  ((c_log++[ERet cpc rcomval cpc'])%list,nlog)
                end
              end
            end
      end
    | RiscMachine.ISA.IJal addr =>
      let ra := Z.of_N (pc+1) in
      let gen_regs' := RiscMachine.RegisterFile.set_register RiscMachine.Register.R_RA ra regs in
      let pc' := addr in
      if SFI.is_same_component_bool pc pc'
      then (c_log,nlog)
      else
        if (N.eqb (SFI.C_SFI pc) SFI.MONITOR_COMPONENT_ID)
        then
          (c_log,nlog)
        else
          let ot := CS.call_trace G pc pc' regs in
          match ot with
          | None => (c_log,nlog)
          | Some t => ((c_log++t)%list,nlog)
          end
    | _ => (c_log,nlog)
    end
  | _ => (c_log,nlog)
  end.

(* 1. number of instr exec, 
   2. number of events in the intermediate trace
   3. number of events in the target trace
   4. result of intermediate program
   5. number of static instructions executed
*)
Definition correct_stat := (nat * nat * nat 
                            * (@execution_state (CompCert.Events.trace*CS.state))
                            * nat)%type.

(* dynamic instr, static instr, 
   # of events in intermediate trace, 
   # of events in target trace,
   intermediate execution result *)
Instance show_correct_stat : Show correct_stat :=
  {|
    show :=
      fun ss =>
        let '(steps, i, t, es, si) := ss in
        (show  steps)
          ++ "," ++ (show si)
           ++ "," ++ (show i )
           ++ "," ++ (show t)
           ++ "," ++ (show es)
  |}.

Definition correct_stats
           (log : correct_log)
           (steps : nat)
           (es : (@execution_state (CompCert.Events.trace*CS.state)))
           (intermTrace : CompCert.Events.trace)
  : correct_stat :=
  let '(l1,l2) := log in
  ( steps, List.length intermTrace, List.length l1, es, List.length l2).

Definition eval_correct_program (fuel : nat)  (p : sfi_program)
  : (@Either (CompCert.Events.trace*MachineState.t*nat) * correct_log ) :=
  ((CS.eval_program_with_state     
     correct_log
     update_correct_log
     fuel
     p
     (RiscMachine.RegisterFile.reset_all)) (nil,nil)).

Definition event_eqb (e1 e2 : CompCert.Events.event) : bool :=
  match (e1,e2) with
  | (ECall c1 p1 v1 c1', ECall c2 p2 v2 c2') => (Component.eqb c1 c2)
                                         && (Procedure.eqb p1 p2)
                                         && (Component.eqb c1' c2')
  | (ERet c1 v1 c1', ERet c2 v2 c2') => (Component.eqb c1 c2)
                                       && (Component.eqb c1' c2')
  | _ => false
  end.

Fixpoint sublist (l1 l2 : CompCert.Events.trace) : bool :=
    match l1 with
    | nil => true
    | x::xs1 =>
       match l2 with
       | nil => false
       | y::xs2 =>
         if event_eqb x y
         then (sublist xs1 xs2)
         else false
       end
    end.
        
      
Definition correct_checker
           (log : correct_log)
           (steps : nat)
           (es : (@execution_state (CompCert.Events.trace*CS.state)))
           (intermTrace : CompCert.Events.trace)
  : Checker :=
  let (l1,l2) := log in
  collect
    (correct_stats log steps es intermTrace)
    (checker (sublist intermTrace l1)) 
.

(* compare traces *)
Definition compiler_correct (t : test_type) (fuel : nat) : Checker :=
  forAllShrink (genIntermediateProgram t) shrink
  ( fun ip =>
      match compile_program ip with
      | CompEitherMonad.Left msg err =>
        whenFail ("Compilation error: " ++ msg ++ newline ++ (show err) ) false
      | CompEitherMonad.Right p =>
        let '(target_res,log) := eval_correct_program fuel p in
        let interm_res := runp fuel ip in
        match interm_res with
        | OutOfFuel _ => checker tt
        | _ =>
          match interm_res with
          | Wrong _ msg InvalidEnv =>
            if DEBUG
            then 
              whenFail ((show interm_res) ++ (show ip))%string false
            else
              checker tt
          | _ => 
            let interm_trace := 
                match interm_res with              
                | Wrong tr _ _ => tr
                | OutOfFuel (tr,_) => tr
                | Halted tr => tr
                | Running (tr,_) => tr (* this should not happen *)
                end in
            match target_res with
            | TargetSFI.EitherMonad.Left msg err =>
              whenFail
                (msg ++ (show err))
                (correct_checker log 0%nat interm_res interm_trace)
            | TargetSFI.EitherMonad.Right (t,(mem,_,regs),steps) =>
              if (Nat.eqb steps fuel)
              then checker tt
              else
                (whenFail
                   (
                     "intermediate trace: "
                       ++ (show interm_trace)
                       ++ " target trace log:" ++ (show (fst log)) ++ newline
                       ++ " target trace t:" ++ (show t) ++ newline
                       ++ "intermediate program: :" ++ (show ip) ++ newline
                       ++ "memory of failed program: " ++ (show_mem  mem)
                   )%string
                   (correct_checker log steps interm_res interm_trace))
            end
          end
        end
      end
  ).


(* Extract Constant Test.defNumTests => "10".  *)

(* QuickChick (compiler_correct 100%nat). *)

(* QuickChick (compiler_correct 1000%nat). *)

(* QuickChick (compiler_correct 10000%nat). *)
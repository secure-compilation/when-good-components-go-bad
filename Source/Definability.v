Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.PS.

Import ListNotations.

Import Source.

Section Definability.
  Variable p: program.
  Variable ictx: Program.interface.
  Variable mainC: Component.id.
  Variable mainP: Procedure.id.

  (** The definability proof takes an execution trace as its input and builds a
      source context that can produce that trace when linked with the
      appropriate program.  Roughly speaking, it does so by keeping one counter
      for each context component, and using that counter to track how many calls
      or returns have been executed by that component.

      To see how this works, suppose that we have a context with two procedures
      P1 and P2, which live in components C1 and C2.  Given the trace

        ECall mainC P1    0 C1
        ECall C1    P2    1 C2
        ERet  C2          2 C1
        ECall C1    P2    3 C2
        ECall C2    mainP 4 mainC

      we would produce the context *)

  (**   C1 {
          P1() {
            if (local[1] == 0) {
              local[1]++;
              C2.P2(1);
              C1.P1(0);
            } else if (local[1] == 1) {
              local[1]++;
              C2.P2(3);
              C1.P1(0);
            } else {
              exit();
            }
          }
        }

        C2 {
          P2() {
            if (local[1] == 0) {
              local[1]++;
              return 2;
            } else if (local[1] == 1) {
              local[1]++;
              mainC.mainP(4);
              C2.P2(0);
            } else {
              exit();
            }
          }
        } *)

   (** Notice that each branch that performs call performs a recursive call at
       the end.  This is needed to trigger multiple events from a single
       function.

       To build a context as above, we traverse the trace of events while
       keeping track of the following data:

   *)

  Inductive state := State {
    (* Some P if the program is currently executing a context procedure P;
       otherwise None. *)
    cur_proc : option Procedure.id;

    (* Call stack with calling procedures. *)
    callers  : list (option Procedure.id);

    (* Function that maps component ids in the context to

         (1) a counter indicating how many events that component has emitted
             thus far, and;

         (2) for each procedure in that component, the code it has executed thus
             far.  This code is represented with a list of pairs (n, e) : Z *
             expr.  The idea is that e is an expression that emits one of the
             events encountered in the trace thus far, and n is how many events
             were emitted earlier by that component. *)
    procs    : PMap.t (Z * PMap.t (list (Z * expr)))

  }.

  (** We start building the context from the following state.  Initially, the
      current procedure is set to mainC, there are no callers, and every
      procedure has no code.  Note that the actual current procedure takes into
      account whether mainC belongs to the context or not. *)
  Definition initial_state : state :=
    let init_procs :=
      PMap.map (fun procs =>
                  (0%Z,
                   fold_left (fun code_procs P => PMap.add P [] code_procs)
                             (Component.export procs) (@PMap.empty _)))
               ictx in
    match PMap.find mainC ictx with
    | Some _ => State (Some mainC) [] init_procs
    | None   => State None         [] init_procs
    end.

  Definition cur_comp (e: event) : Component.id :=
    match e with
    | ECall C _ _ _ => C
    | ERet  C _ _   => C
    end.

  (** Given the current event and the call stack, compute the next value of
      cur_proc. *)
  Definition next_proc (e: event) (callers: list (option Procedure.id)) : option Procedure.id :=
    match e with
    | ECall _ next_proc _ next_comp =>
      match PMap.find next_comp ictx with
      | Some _ => Some next_proc
      | None   => None
      end
    | ERet _ _ next_comp =>
      match callers with
      | [] => (* Should never happen *) None
      | next_proc :: callers' =>
        match PMap.find next_comp ictx with
        | Some _ => next_proc
        | None   => None
        end
      end
    end.

  (** Compute the next value of callers. *)
  Definition next_callers
    (e: event)
    (cur_proc: option Procedure.id)
    (callers: list (option Procedure.id)) : list (option Procedure.id) :=
    match e with
    | ECall _ _ _ _ => cur_proc :: callers
    | ERet _ _ _ => tail callers
    end.

  (** Given an event e, compute the expression needed to produce that event.
      That expression will be added to the code of the current procedure
      below. *)
  Definition next_instr (e: event) : expr :=
    match e with
    | ECall _ next_proc arg next_comp =>
      E_call next_comp next_proc (E_val (Int arg))
    | ERet  _ ret_val _ => E_val (Int ret_val)
    end.

  (** Update the state of the context building procedure with an event. *)
  Definition update_state (ps: state) (e: event) : state :=
    let 'State cur_proc callers procs := ps in
    (* Test whether the call was performed from the context *)
    match PMap.find (cur_comp e) procs, cur_proc with
    | Some (n_events, cur_comp_procs), Some cur_proc =>
      (* If so, add a corresponding instruction to the code of the calling
         procedure *)
      match PMap.find cur_proc cur_comp_procs with
      | Some code =>
        {| cur_proc := next_proc e callers;
           callers  := next_callers e (Some cur_proc) callers;
           procs    :=
             PMap.add (cur_comp e)
                      (Z.succ n_events,
                       PMap.add cur_proc (code ++ [(n_events, next_instr e)]) cur_comp_procs)
                      procs |}
      | None =>
        (* This branch should never be executed, as there should be code for
           all procedures present here. *)
        ps
      end
    | _, _ =>
      (* If not, simply update cur_proc and callers. *)
      {| cur_proc := next_proc e callers;
         callers  := next_callers e cur_proc callers;
         procs    := procs |}
    end.

  (** After we apply update_state to all the events in the trace,
      linearize_instructions converts the representation of each procedure into
      the chain of if statements depicted above. *)
  Definition linearize_instructions
    (C: Component.id)
    (P: Procedure.id)
    (instrs: list (Z * expr)) : expr :=
    let one := E_val (Int 1%Z) in
    let count := E_binop Add E_local one in
    let add_instruction p e :=
        let '(pos, instr) := p in
        E_if (E_binop Eq count (E_val (Int pos)))
             (E_seq (E_assign count (E_binop Add (E_deref count) one))
                    (E_seq instr (E_call C P one)))
             e in
    fold_right add_instruction E_exit instrs.

  (** Combine all of the above steps to convert a trace into a context. *)
  Definition build_context (t: trace) :=
    let 'State cur_proc callers procs :=
        fold_left update_state t initial_state in
    PMap.mapi (fun C p =>
                 let '(count, comp_procs) := p in
                 PMap.mapi (linearize_instructions C) comp_procs) procs.

  Theorem context_definability:
    forall t beh,
      program_behaves (PS.sem p ictx) (behavior_app t beh) ->
    exists ctx,
      PMap.Equal (prog_interface ctx) ictx /\
      program_behaves (CS.sem (program_link p ctx mainC mainP)) (Terminates t).
  Proof.
  Admitted.
End Definability.

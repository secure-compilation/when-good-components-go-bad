Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import CompCert.Events.

Require Import Common.Definitions.
Require Import Common.Maps.

Require Import Intermediate.Machine.

Require Import I2SFI.CompTestUtil.

Require Import CoqUtils.ord.

From mathcomp Require Import ssreflect ssrfun ssrbool ssreflect.eqtype.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Definition DEPTH := 5%nat.

Definition Procedure := (Component.id * Procedure.id)%type.

Definition Node :=  (Procedure * nat * (list Procedure))%type.

Definition CallGraph := list Node.

Theorem proc_eq_dec :  forall l1 l2 : Procedure,  {l1 = l2} + {l1 <> l2}.
Proof.
  repeat decide equality. Defined.

Theorem callGraph_eq_dec :  forall g1 g2 : CallGraph,  {g1 = g2} + {g1 <> g2}.
Proof.
  repeat decide equality. Defined.

Definition proc_eqb (p1 : Procedure) (p2 : Procedure) : bool :=
  andb (Nat.eqb (fst p1) (fst p2))
       (Nat.eqb (snd p1) (snd p2)).

Definition nodeGetCid (v : Node) : Component.id :=
  fst (fst (fst v)).

Definition nodeGetPid (v : Node) : Procedure.id :=
  snd (fst (fst v)).

Definition nodeGetProcedure (v : Node) : Procedure :=
  fst (fst v).

Definition nodeGetDepth (v : Node) : nat :=
  snd (fst v).

Definition nodeGetCallList (v : Node) : list Procedure :=
  snd v.

Definition existsb (p : Procedure) (cg : CallGraph) : bool :=
  List.existsb
    (fun n => proc_eqb n p)
    (List.map nodeGetProcedure cg).

Definition size (ip : Intermediate.program) : nat :=
  List.fold_left
    (fun acc '(_,pmap) =>
       List.fold_left
         (fun acc' '(_,lc) => (acc' + (List.length lc))%nat )
         (elementsm pmap) acc
    )
    (elementsm (Intermediate.prog_procedures ip)) 0%nat.

Definition buildCallGraph (ip : Intermediate.program) : CallGraph :=
  let fix worker
          (wklst : list (Procedure*nat))
          (acc : CallGraph)
          (sz : nat) := (* sz is a decreasing parameter for termination check *)
      match sz with
      | O => acc
      | S sz' =>
        match wklst with
        | nil => acc
        | (p,depth) :: xs =>
          if existsb p acc
          then worker xs acc sz'
          else
            (* process p *)
            match getm (Intermediate.prog_procedures ip) (fst p) with
            | None => acc
            | Some pmap =>
              match getm pmap (snd p) with
              | None => acc
              | Some lc =>
                let calledProcs :=
                    List.map
                      (fun i =>
                         match i with
                         | ICall cid pid => (cid,pid)
                         | _ => (1%nat,1%nat) (* this is not applicable *)
                         end )
                      (List.filter (fun i =>
                                      match i with
                                      | ICall _ _ => true
                                      | _ => false
                                      end ) lc) in
                let wklst' := (xs ++ (List.map (fun x => (x,(depth+1)%nat)) calledProcs))%list in
                worker wklst' ((p,depth,calledProcs)::acc) sz'
              end
            end
        end
      end in
  match Intermediate.prog_main ip with
  | None => nil
  | Some p => worker [(Component.main,p,0%nat)] nil (size ip)
  end.

Definition  shrinkNode (pn:Node) : (list (list Procedure)) :=
  let p := nodeGetProcedure pn in
  let depth := nodeGetDepth pn in
  let lp := nodeGetCallList pn in
  (* shrink head *)
  let n := List.length lp in
  List.map (fun nn => List.firstn nn lp)
           (List.rev (List.seq 0%nat (List.length lp))).


Definition find (p : Procedure) (cg : CallGraph) : option Node :=
  List.find
    (fun v => proc_eqb p (nodeGetProcedure v) )
    cg.

Definition shrinkCallGraph (main : Procedure)  (cg : CallGraph) : (list CallGraph) :=

  let fix worker
          (wklst : list Procedure)
          (acc : CallGraph)
          (cg : CallGraph)
          (sz : nat) := (* sz is a decreasing parameter for termination check *)
      match sz with
      | O => [acc]
      | S sz' =>
        match wklst with
        | nil => [acc]
        | p :: xs =>
          if existsb p acc
          then (* node already in generated graph *)
            worker xs acc cg sz'
          else (* node not processed yet *)
            match find p cg with
            | None => [acc] (* this should not happen *)
            | Some n =>
              let depth := nodeGetDepth n in
              let calls := nodeGetCallList n in
              if Nat.ltb depth DEPTH
              then (* this node can be shrunk*)
                (* shrink the node and not the procedures it calls *)
                ((List.flat_map
                    ( fun (newCallList : list Procedure) =>
                        worker
                          xs  (* worklist *)
                          (* accumulator : add all procedures in newCallList
                             that are not already in *)
                          (List.fold_left
                             (fun acc' p' =>
                                if existsb p' acc'
                                then acc'
                                else
                                  match find p' cg with
                                  | None => acc'
                                  | Some x => acc' ++ [x]
                                  end
                             )
                             newCallList
                             (acc ++ [(p,depth,newCallList)])
                          )
                          cg sz'
                    )
                    (shrinkNode n))
                   ++
                   (
                     worker (xs++calls) (acc++[n]) cg sz'
                   )
                )%list
              else (* node not in graph, but depth too big *)
                worker xs (acc++[n]) cg sz'
            end
        end
      end in
  match find main cg with
  | None => nil
  | Some nodeMain =>
    List.remove
      callGraph_eq_dec (* just in case the original program slips in *)
      cg
      (worker [(nodeGetProcedure nodeMain)]
              nil
              cg
              (1+ (List.fold_left
                     ( fun acc v => (acc + (List.length (nodeGetCallList v)))%nat )
                     cg 0%nat))%nat
      )
  end.

Definition getComponents (cg : CallGraph) : list Component.id :=
  List.nodup Nat.eq_dec (List.map (fun n => nodeGetCid n ) cg).

Definition buildInterface (components : list Component.id)
           (cg : CallGraph) : (Program.interface) :=
  List.fold_left
    (
      fun acc cid =>
        let newExport :=
            List.nodup
              Nat.eq_dec
              (
                List.map
                  nodeGetPid
                  (List.filter
                     (fun n => Component.eqb (nodeGetCid n) cid)
                     cg)
              )
        in
        let newImport := (* all the called procs by this component *)
            List.nodup proc_eq_dec
                       ( List.fold_left
                           (fun acc' n =>
                              if Component.eqb (nodeGetCid n) cid
                              then
                                acc' ++ (nodeGetCallList n)
                              else acc'
                           ) cg nil
                       ) in

        let newcint := Component.mkCompInterface (list2fset newExport)
                                                 (list2fset newImport)
        in
        setm acc cid newcint
    )
    components
    emptym.

Definition buildProcedures (components : list Component.id)
           (cg : CallGraph)
           (ip : Intermediate.program) : NMap (NMap code) :=
  let all_procs :=
      List.fold_left
        (fun acc n => (nodeGetProcedure n)::acc) cg nil in
  let all_code :=
      List.fold_left
        (fun acc '(p,_,callList) =>
        let cid := fst p in
        let pid := snd p in
        match getm (Intermediate.prog_procedures ip) cid with
        | None => acc
        | Some pmap =>
          let oldmap := (match getm acc cid with
                         | None => emptym
                         | Some x => x
                         end) in
          match getm pmap pid with
          | None => acc
          | Some lcode =>
            let newcode := List.map
                             ( fun i =>
                                 match i with
                                 | ICall c' p' =>
                                   if (List.existsb (fun p => proc_eqb p (c',p') ) all_procs)
                                   then i
                                   else INop
                                 | _ => i
                                 end
                             )
                             lcode in
            setm acc cid (setm oldmap pid newcode)
          end
        end
     )
     cg
     emptym in

  mapm
    ( fun pmaps =>


        let declared :=
            List.fold_left
              (fun acc '(pid,li) =>
                 List.fold_left
                   (fun acc' i =>
                      match i with
                      | ILabel l => l::acc'
                      | _ => acc'
                      end) li acc
              ) (elementsm pmaps) nil
        in

        mapm
          (fun li =>
             List.map
               (fun i =>
                  match i with
                  | IJal l =>
                    if (List.existsb (fun l' => Nat.eqb l' l) declared)
                    then i
                    else INop
                  | IBnz _ l =>
                    if (List.existsb (fun l' => Nat.eqb l' l) declared)
                    then i
                    else INop
                  | _ => i
                  end) li
          ) pmaps
    )
    all_code
.

Definition buildBuffers (components : list Component.id)
           (cg : CallGraph)
           (ip : Intermediate.program)
  : {fmap nat_ordType -> {fmap Block.id -> nat + list value}}  :=
  List.fold_left
    ( fun acc cid =>
        match (Intermediate.prog_buffers ip) cid with
        | None => acc
        | Some x => setm acc cid x
        end
    )
    components
    emptym.

Definition buildIntermediateProgram (cg : CallGraph)
           (ip : Intermediate.program) : Intermediate.program :=
  let components := getComponents cg in
  {|
    Intermediate.prog_interface := buildInterface components cg;
    Intermediate.prog_procedures := buildProcedures components cg ip;
    Intermediate.prog_buffers := buildBuffers components cg ip;
    Intermediate.prog_main := (Intermediate.prog_main ip)
  |}.

Definition list_eqb {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  andb
    (List.fold_left
       (
         fun acc x => andb (List.existsb (eqb x) l1) acc
       )
       l2 true)
    (List.fold_left
       (
         fun acc x => andb (List.existsb (eqb x) l2) acc
       )
       l1 true).

Definition interface_contained (small : Program.interface)
           (big : Program.interface) : bool :=
  List.fold_left
    (fun acc '(cid,cint) =>
       if acc
       then
         match getm big cid with
         | None => false
         | Some bigCint =>
           if list_eqb Nat.eqb (val (Component.export cint)) (val (Component.export bigCint))
           then
             list_eqb proc_eqb (val (Component.import cint)) (val (Component.import bigCint))
           else false
         end
       else false
    )
    (elementsm small) true.

Instance shrinkIntermediateProgram : Shrink Intermediate.program :=
  {|
    shrink :=
      fun ip =>
        match Intermediate.prog_main ip with
        | None => nil
        | Some mainP =>
          (* must deal with the case the program represented by
             the call graph is already smallest and not the same
             as the original *)
          let cg := buildCallGraph ip in
          let newip := buildIntermediateProgram cg ip in
          let newCallGraphs := shrinkCallGraph (Component.main, mainP) cg in
          let shrinked := List.map (fun ncg => buildIntermediateProgram ncg ip) newCallGraphs in
          if interface_contained (Intermediate.prog_interface ip)
               (Intermediate.prog_interface newip)
          then shrinked
          else newip::shrinked
        end
  |}.

(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.

Require Import CompCert.Events.

Require Import I2SFI.Compiler.
Require Import I2SFI.AbstractMachine.
Require Import TargetSFI.EitherMonad.
Require Import TargetSFI.Machine.
Require Import CompEitherMonad.
Require Import CompStateMonad.
Require Import TargetSFI.CS.
Require Import Intermediate.Machine.
Require Import Common.Definitions.
Require Import Common.Maps.

Import MonadNotations.
Open Scope monad_scope.

Definition test (instrs : Intermediate.Machine.code) 
  : @Either (trace*MachineState.t) :=
  let COMP1_ID : positive := 1%positive in
  let PROC1_ID : positive := 1%positive in
  let BLOCK1_ID : positive := 1%positive in
  let component1_interface : Component.interface :=
      (Component.mkCompInterface [PROC1_ID] []) in
  let program_interface : Program.interface :=
      PMap.add COMP1_ID component1_interface (PMap.empty Component.interface) in
  let buffers := PMap.add COMP1_ID [(BLOCK1_ID,(inl 10%nat))] (PMap.empty (list (Block.id * (nat + list value)))) in
  let proc1_code := (PMap.add PROC1_ID (instrs++[Intermediate.Machine.IReturn])
                              (PMap.empty Intermediate.Machine.code) ) in
  let procs := PMap.add COMP1_ID proc1_code
                        (PMap.empty (PMap.t Intermediate.Machine.code)) in
  let program : Intermediate.program := {|
        Intermediate.prog_interface := program_interface;
        Intermediate.prog_procedures := procs;
        Intermediate.prog_buffers := buffers;
        Intermediate.prog_main := (COMP1_ID,PROC1_ID)
      |} in
  match compile_program program with
  | CompEitherMonad.Left msg err => EitherMonad.Left msg EitherMonad.NoInfo
  | CompEitherMonad.Right p =>
    CS.eval_program (100%nat) p RiscMachine.RegisterFile.reset_all
  end.

Example test_INop :
  exists (pc : RiscMachine.address)
    (mem : RiscMachine.Memory.t) 
    (gen_regs : RiscMachine.RegisterFile.t),
  test [Intermediate.Machine.INop] = EitherMonad.Right (E0,(mem,pc,gen_regs)).
Proof.  
  compute. eauto. Qed.

Example test_IConst :
  exists (pc : RiscMachine.address)
    (mem : RiscMachine.Memory.t) 
    (gen_regs : RiscMachine.RegisterFile.t),
    test [Intermediate.Machine.IConst (IInt 5%Z) R_AUX1] =
    EitherMonad.Right (E0,(mem,pc,gen_regs)) /\
    (RiscMachine.RegisterFile.get_register RiscMachine.Register.R_AUX1 gen_regs = Some 5%Z)
.
Proof.  
  compute. eauto. Qed.

Example test_IMov :
  exists (pc : RiscMachine.address)
    (mem : RiscMachine.Memory.t) 
    (gen_regs : RiscMachine.RegisterFile.t),
    (RiscMachine.RegisterFile.get_register RiscMachine.Register.R_AUX1 gen_regs = Some 5%Z) /\
    (RiscMachine.RegisterFile.get_register RiscMachine.Register.R_AUX2 gen_regs = Some 5%Z)
    ->
    test [Intermediate.Machine.IConst (IInt 5%Z) R_AUX1 
          ;Intermediate.Machine.IMov R_AUX1 R_AUX2] =
    EitherMonad.Right (E0,(mem,pc,gen_regs)).   
Proof.  
  compute. eauto. Qed.

Example test_IStore :
  exists (pc : RiscMachine.address)
    (mem : RiscMachine.Memory.t) 
    (gen_regs : RiscMachine.RegisterFile.t),
    (RiscMachine.RegisterFile.get_register RiscMachine.Register.R_AUX1 gen_regs =
     Some (RiscMachine.to_value (SFI.address_of 1%N 3%N 0%N))) /\
    (RiscMachine.RegisterFile.get_register RiscMachine.Register.R_AUX2 gen_regs = Some 5%Z) /\
    (RiscMachine.Memory.get_value mem (SFI.address_of 1%N 3%N 0%N) = Some 5%Z)
    ->
    test  [Intermediate.Machine.IConst (IPtr (1%positive,1%positive,0%Z) ) R_AUX1 
           ; Intermediate.Machine.IConst (IInt 5%Z) R_AUX2 
           ; Intermediate.Machine.IStore R_AUX1 R_AUX2]  =
    EitherMonad.Right (E0,(mem,pc,gen_regs)).   
Proof.  
  compute. eauto. Qed.

Example test_ILoad :
  exists (pc : RiscMachine.address)
    (mem : RiscMachine.Memory.t) 
    (gen_regs : RiscMachine.RegisterFile.t),
    (RiscMachine.RegisterFile.get_register RiscMachine.Register.R_AUX1 gen_regs =
     Some (RiscMachine.to_value (SFI.address_of 1%N 3%N 0%N))) /\
    (RiscMachine.RegisterFile.get_register RiscMachine.Register.R_AUX1 gen_regs = Some 5%Z) /\
    (RiscMachine.Memory.get_value mem (SFI.address_of 1%N 3%N 0%N) = Some 5%Z)
    ->
    test  [Intermediate.Machine.IConst (IPtr (1%positive,1%positive,0%Z) ) R_AUX1 
               ; Intermediate.Machine.IConst (IInt 5%Z) R_AUX2
               ; Intermediate.Machine.IStore R_AUX1 R_AUX2
               ; Intermediate.Machine.IMov R_AUX1 R_AUX2
               ; Intermediate.Machine.ILoad R_AUX2 R_AUX1
        ]  =
    EitherMonad.Right (E0,(mem,pc,gen_regs)).   
Proof.  
  compute. eauto. Qed.

Example test_IBnz :
  exists (pc : RiscMachine.address)
    (mem : RiscMachine.Memory.t) 
    (gen_regs : RiscMachine.RegisterFile.t),
    (SFI.C_SFI pc = SFI.MONITOR_COMPONENT_ID)
    ->
    test [Intermediate.Machine.ILabel 7%positive 
               ;Intermediate.Machine.IConst (IPtr (1%positive,1%positive,0%Z) ) R_AUX1
               ; Intermediate.Machine.IConst (IInt 5%Z) R_AUX2
               ; Intermediate.Machine.IStore R_AUX1 R_AUX2
               ; Intermediate.Machine.IMov R_AUX1 R_AUX2
               ; Intermediate.Machine.ILoad R_AUX2 R_AUX1
               ; Intermediate.Machine.IConst (IInt 0%Z) R_AUX1
               ; Intermediate.Machine.IBnz R_AUX1 7%positive]  =
    EitherMonad.Right (E0,(mem,pc,gen_regs)).   
Proof.  
  compute. eauto. Qed.

Example test_IAlloc_Initial_Value :
  exists (pc : RiscMachine.address)
    (mem : RiscMachine.Memory.t) 
    (gen_regs : RiscMachine.RegisterFile.t),
    test [
        Intermediate.Machine.INop
      ] =
    EitherMonad.Right (E0,(mem,pc,gen_regs)) /\
    (*  expect cid=1 slot=1 offset=0 has value 1 *)    
    ((RiscMachine.Memory.get_value mem (SFI.address_of 1%N 1%N 0%N))
     = Some 1).
Proof.  
  compute. eauto. Qed.


Example test_Alloc :
  exists (pc : RiscMachine.address)
    (mem : RiscMachine.Memory.t) 
    (gen_regs : RiscMachine.RegisterFile.t),
    test [
        Intermediate.Machine.IAlloc R_AUX1 R_AUX2
      ] =
    EitherMonad.Right (E0,(mem,pc,gen_regs))
    /\ ((RiscMachine.Memory.get_value mem (SFI.address_of 1%N 1%N 0%N))
     = Some 2) 
.
Proof.  
  compute. eauto. Qed.


Example test_IAlloc1 :
  exists (pc : RiscMachine.address)
    (mem : RiscMachine.Memory.t) 
    (gen_regs : RiscMachine.RegisterFile.t),
    test [
        Intermediate.Machine.IAlloc R_AUX1 R_AUX2
        ; Intermediate.Machine.IConst (IInt 5%Z) R_AUX2
        ; Intermediate.Machine.IStore R_AUX1 R_AUX2
         ] =
    EitherMonad.Right (E0,(mem,pc,gen_regs)) 
    /\ ((RiscMachine.Memory.get_value mem (SFI.address_of 1%N 5%N 0%N)) = Some 5%Z)
.
Proof.  
  compute. eauto. Qed.

Example test_layout_procedure :
  layout_procedure 1%positive 1%positive (1%positive,8%N)
                   [
                     AbstractMachine.IHalt
                     ; AbstractMachine.ILabel (1%positive,8%N)
                     ; AbstractMachine.IJump RiscMachine.Register.R_SP
                     ; AbstractMachine.IJump RiscMachine.Register.R_SP
                   ]
  =
  [
    (None, AbstractMachine.IHalt)
    ; ( Some [(1%positive,8%N)], AbstractMachine.IJump RiscMachine.Register.R_SP)
    ; ( None, AbstractMachine.IJump RiscMachine.Register.R_SP)
  ].
Proof.
  compute. eauto. Qed.


Example test_layout_procedure1 :
  layout_procedure 1%positive 1%positive (1%positive,8%N)
                   [
                     AbstractMachine.IHalt
                     ; AbstractMachine.ILabel (1%positive,8%N)
                     ; AbstractMachine.IJump RiscMachine.Register.R_SP
                     ; AbstractMachine.IJump RiscMachine.Register.R_SP
                     ; AbstractMachine.ILabel (1%positive,4%N)
                     ; AbstractMachine.IJump RiscMachine.Register.R_AUX1
                     ; AbstractMachine.IJump RiscMachine.Register.R_AUX2
                   ]
  =
  [
    (None, AbstractMachine.IHalt)
    ; ( Some [(1%positive,8%N)], AbstractMachine.IJump RiscMachine.Register.R_SP)
    ; ( None, AbstractMachine.IJump RiscMachine.Register.R_SP)
    ; ( None, AbstractMachine.INop)
    ; ( None, AbstractMachine.INop)
    ; ( None, AbstractMachine.INop)
    ; ( None, AbstractMachine.INop)
    ; ( None, AbstractMachine.INop)
    ; ( None, AbstractMachine.INop)
    ; ( None, AbstractMachine.INop)
    ; ( None, AbstractMachine.INop)
    ; ( None, AbstractMachine.INop)
    ; ( None, AbstractMachine.INop)
    ; ( None, AbstractMachine.INop)
    ; ( None, AbstractMachine.INop)
    ; ( None, AbstractMachine.INop)
    ; ( Some [(1%positive,4%N)], AbstractMachine.IJump RiscMachine.Register.R_AUX1)
    ; ( None, AbstractMachine.IJump RiscMachine.Register.R_AUX2)
  ].
Proof.
  compute. eauto. Qed.
 

Example test_layout_procedure_no_padding :
  layout_procedure 1%positive 1%positive (1%positive,8%N)
                   ( [
                     AbstractMachine.IHalt
                     ; AbstractMachine.ILabel (1%positive,8%N)
                   ]
                   ++ ( List.repeat (AbstractMachine.IJump RiscMachine.Register.R_SP)
                                    ((N.to_nat SFI.BASIC_BLOCK_SIZE) - 1) )
                   ++  [
                     AbstractMachine.ILabel (1%positive,4%N)
                     ; AbstractMachine.IJump RiscMachine.Register.R_AUX1
                     ; AbstractMachine.IJump RiscMachine.Register.R_AUX2
                   ] )
  = [
    (None, AbstractMachine.IHalt)
    ; ( Some [(1%positive,8%N)], AbstractMachine.IJump RiscMachine.Register.R_SP)
  ]
      ++ ( List.repeat
                 ((None, AbstractMachine.IJump RiscMachine.Register.R_SP))
                  ((N.to_nat SFI.BASIC_BLOCK_SIZE) - 2) )
      ++ [ ( Some [(1%positive,4%N)], AbstractMachine.IJump RiscMachine.Register.R_AUX1)
           ; ( None, AbstractMachine.IJump RiscMachine.Register.R_AUX2)].
Proof.
  compute. eauto. Qed.


Example exported_procs_labels_test :
  PMap.equal (PMap.equal label_eqb)
    ( exported_procs_labels
        (PMap.add 1%positive
                  (PMap.add 2%positive
                            [
                              Intermediate.Machine.IConst (IInt 1%Z) R_ONE
                              ; Intermediate.Machine.IJal 1%positive
                              ; Intermediate.Machine.IHalt
                            ]
                  (PMap.add 1%positive
                            [
                              Intermediate.Machine.IConst (IInt 1%Z) R_ONE
                              ; Intermediate.Machine.IJal 1%positive
                              ; Intermediate.Machine.IReturn
                              ; Intermediate.Machine.ILabel 1%positive
                              ; Intermediate.Machine.IMov R_SP R_AUX1
                              ; Intermediate.Machine.IConst (IInt 20%Z) R_SP
                              ; Intermediate.Machine.IAlloc R_SP R_SP
                              ; Intermediate.Machine.IStore R_SP R_AUX1
                              ; Intermediate.Machine.IBinOp Common.Values.Add R_SP R_ONE R_SP
                              ; Intermediate.Machine.IConst (IPtr (1%positive,1%positive,0%Z))
                                                            R_AUX1
                              ; Intermediate.Machine.ILoad R_AUX1 R_AUX1
                              ; Intermediate.Machine.IStore R_SP R_AUX1
                              ; Intermediate.Machine.IBinOp Common.Values.Add R_SP R_ONE R_SP
                              ; Intermediate.Machine.IConst (IPtr (1%positive,1%positive,0%Z))
                                                            R_AUX2
                              ; Intermediate.Machine.IStore R_AUX2 R_COM
                              ; Intermediate.Machine.IConst (IPtr (1%positive,1%positive,0%Z))
                                                            R_COM
                              ; Intermediate.Machine.ILoad R_COM R_COM
                              ; Intermediate.Machine.IBinOp Common.Values.Minus R_SP R_ONE R_SP
                              ; Intermediate.Machine.ILoad R_SP R_AUX1
                              ; Intermediate.Machine.IConst (IPtr (1%positive,1%positive,0%Z))
                                                            R_AUX2
                              ; Intermediate.Machine.IStore R_AUX2 R_AUX1
                              ; Intermediate.Machine.IBinOp Common.Values.Minus R_SP R_ONE R_SP
                              ; Intermediate.Machine.ILoad R_SP R_SP
                              ; Intermediate.Machine.IJump R_RA
                            ]
                            (PMap.empty Intermediate.Machine.code))
                  ) (PMap.empty  (PMap.t Intermediate.Machine.code)))
      (PMap.add 1%positive
               (Component.mkCompInterface [1%positive;2%positive] [])
               (PMap.empty Component.interface))
                  
    )
    (
      (PMap.add 1%positive
                (PMap.add 2%positive
                          (1%positive,3%N)
                 (PMap.add 1%positive
                           (1%positive,2%N)
                           (PMap.empty AbstractMachine.label))
                 ) (PMap.empty  (PMap.t AbstractMachine.label)))
    ) = true.
Proof.
  compute. eauto. Qed.

Example exported_procs_labels_test2 :
  PMap.equal
    (PMap.equal label_eqb)
    ( exported_procs_labels
        (PMap.add 2%positive                  
                  (PMap.add 1%positive
                            [
                              Intermediate.Machine.IConst (IInt 1%Z) R_ONE
                              ; Intermediate.Machine.IJal 2%positive
                              ; Intermediate.Machine.IReturn
                              ; Intermediate.Machine.ILabel 2%positive
                              ; Intermediate.Machine.IMov R_SP R_AUX1
                              ; Intermediate.Machine.IAlloc R_SP R_SP
                              ; ICall 2%positive 1%positive
                              ; Intermediate.Machine.IJump R_RA
                            ]
                            (PMap.empty Intermediate.Machine.code))
                  (PMap.add 1%positive
                            (PMap.add 3%positive
                                      [
                                        Intermediate.Machine.IConst (IInt 1%Z) R_ONE
                                        ; Intermediate.Machine.IJal 1%positive
                                        ; Intermediate.Machine.IHalt
                                      ]
                                      (PMap.add 1%positive
                                                [
                                                  Intermediate.Machine.IConst (IInt 1%Z) R_ONE
                                                  ; Intermediate.Machine.IJal 1%positive
                                                  ; Intermediate.Machine.IReturn
                                                  ; Intermediate.Machine.ILabel 1%positive
                                                  ; Intermediate.Machine.IMov R_SP R_AUX1
                                                  ; Intermediate.Machine.IAlloc R_SP R_SP
                                                  ; Intermediate.Machine.IJump R_RA
                                                ]
                                                (PMap.empty Intermediate.Machine.code))
                            ) (PMap.empty  (PMap.t Intermediate.Machine.code))))
        (PMap.add 2%positive
                  (Component.mkCompInterface [1%positive] [])
                  (PMap.add 1%positive
                            (Component.mkCompInterface [1%positive;3%positive]
                                                       [(2%positive,1%positive)])
                            (PMap.empty Component.interface)))                  
    )
    (
      PMap.add 2%positive
               (PMap.add 1%positive
                          (2%positive,3%N)
                          (PMap.empty AbstractMachine.label))
               (PMap.add 1%positive
                         (PMap.add 1%positive
                                   (1%positive,2%N)
                                   (PMap.add 3%positive
                                             (1%positive,3%N)
                                             (PMap.empty AbstractMachine.label)))
                         (PMap.empty  (PMap.t AbstractMachine.label)))
    ) = true.
Proof.
  compute. eauto. Qed.


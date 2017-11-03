(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapAVL.

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Maps.
Require Import SFIUtil.
Require Import StateMonad.

From mathcomp.ssreflect Require Import ssreflect ssrbool eqtype.

Import BinNatMapExtra.

(******************************************
 * Basic Risc Machine Definition
 *******************************************)
Module RiscMachine.

  Definition value := Z.

  Definition immediate := Z.

  Definition address := N.

  (* program counter register type *)
  Definition pc : Set := address.

  Definition PC0 : pc := N0.

  (******************************************
   * Register Type Definition
   *******************************************)
  Module Register.
    
    Open Scope N_scope.
    Definition t := N.

    Definition R_ONE: t := 1.
    Definition R_COM : t := 2.
    Definition R_AUX1 : t := 3.
    Definition R_AUX2 : t := 4.
    Definition R_RA : t := 5.
    Definition R_SP : t := 6. 
    (* reserved SFI registers *)
    Definition R_SFI_SP: t := 26.
    Definition R_AND_CODE_MASK : t := 27.
    Definition R_AND_DATA_MASK : t := 28.
    Definition R_OR_CODE_MASK : t := 29.
    Definition R_OR_DATA_MASK : t := 30.
    Definition R_T : t := 31.
    Definition R_D : t := 32.    
    Close Scope N_scope.
    
    Definition NO_REGISTERS : nat := 33.
    
    (* Definition IS_NOT_SFI_REGISTER (reg:N) := reg < 26. *)
    (* Definition IS_SFI_REGISTER (reg:N) := reg > 25. *)
    (* Definition is_not_sfi_reg_bool (reg:N) := reg <? 26.     *)
    (* Definition  IS_SFI_SP_REGISTER (reg:N) := reg = 26.     *)
    (* Definition is_sfi_sp_register_bool (reg:N) := reg =? 26. *)

    Definition eqb (r1 r2 : t) : bool :=
      N.eqb r1 r2.

    Theorem eqb_eq:
      forall r1 r2 : t, eqb r1 r2 = true <-> r1 = r2.
    Proof.
      intros r1 r2. apply N.eqb_eq.
    Qed.

    Theorem eqb_refl:
      forall r : t, eqb r r = true.
    Proof. apply N.eqb_refl. Qed.
    
  End Register.


  (******************************************************
   * Register File Definition 
   * General Registers (does not contain program counter)
   ******************************************************)
  Module RegisterFile <: UsualDecidableType.

    (* Use the constants in the Register Module as indices in the list,
       to get the value of the register *)
    Definition t : Set := list value.

    Fixpoint is_zero (gen_regs:t)  : Prop :=
      match gen_regs with
      | [] => True
      | r :: l' => (r = Z0 )/\ is_zero l'
      end.

    Definition reset_all : t := repeat Z0 Register.NO_REGISTERS.

    Definition set_register (reg : Register.t) (val : value)
               (gen_regs  : t) : t :=
      Util.Lists.update gen_regs (N.to_nat reg) val.

    Definition get_register (reg : Register.t) (gen_regs : t) : option value :=
      ListUtil.get (N.to_nat reg) gen_regs.

    Fixpoint eqb (regs1 regs2 : t) : bool :=
      match (regs1,regs2) with
      | ([],[]) => true
      | (v1::regs1',v2::regs2') => (Z.eqb v1 v2) && (eqb regs1' regs2')
      | _ => false
      end.

    Lemma eqb_refl:
      forall regs, eqb regs regs = true.
    Proof.
      intros.
      induction regs.
      - reflexivity.
      - simpl.
        rewrite Z.eqb_refl. rewrite IHregs.
        reflexivity.
    Qed.
    
    
    Lemma eqb_eq: forall (regs1 regs2 : t),
        (eqb regs1 regs2) = true <-> regs1 = regs2.
    Proof.
      split.
      - intro H. generalize dependent regs2. induction regs1.
        + intros. destruct regs2.
          * reflexivity.
          * inversion H.
        + intros. destruct regs2.
          * inversion H.
          * inversion H. apply andb_true_iff in H1.
            destruct H1 as [Hh Ht].
            apply IHregs1 in Ht.
            rewrite Ht.
            apply Z.eqb_eq in Hh. 
            rewrite Hh. reflexivity.
      - intro H. rewrite H. apply eqb_refl.
    Defined.


    Lemma neqb_neq: forall (regs1 regs2 : t),
        (eqb regs1 regs2) = false -> regs1 <> regs2.
    Proof.
      intros. intro H1. apply eqb_eq in H1. rewrite H1 in H. inversion H.
    Qed.
                                                             
        
    Theorem eq_dec: forall regs1 regs2 : t, {regs1 = regs2} + {regs1 <> regs2}.
    Proof.
      apply List.list_eq_dec. apply Z.eq_dec.
      (* induction regs1. *)
      (* - destruct regs2. *)
      (*   + auto. *)
      (*   + right. intro H. inversion H. *)
      (* - destruct regs2. *)
      (*   + right. intro H. inversion H. *)
      (*   + destruct (Z.eqb a v) eqn:Hh. *)
      (*     * rewrite Z.eqb_eq in Hh. rewrite Hh. *)
      (*       destruct IHregs1 with (regs2:=regs2). *)
      (*       left. apply f_equal. apply e. *)
      (*       right. intro H. apply n. inversion H. reflexivity. *)
      (*     * right. intro H. inversion H. rewrite <- Z.eqb_eq in H1. *)
      (*       rewrite Hh in H1. inversion H1. *)
    Defined.


    Include HasUsualEq <+ UsualIsEq.

  End RegisterFile.


  (******************************************************
   * ISA Definitions: Instructions and binary operations
   ******************************************************)
  Module ISA.
    
    Inductive binop : Type :=
    | Addition : binop
    | Subtraction : binop
    | Multiplication : binop
    | Equality : binop
    | Leq : binop
    | BitwiseOr : binop
    | BitwiseAnd : binop
    | ShiftLeft : binop.
  
    Inductive instr : Set :=
    | INop : instr
    (* register operations *)
    | IConst : value -> Register.t -> instr
    | IMov : Register.t -> Register.t -> instr
    | IBinOp : binop -> Register.t -> Register.t -> Register.t -> instr
    (* memory operations *)
    | ILoad : Register.t -> Register.t -> instr
    | IStore : Register.t -> Register.t -> instr
    (* conditional and unconditional jumps *)
    | IBnz : Register.t -> immediate -> instr
    | IJump : Register.t -> instr
    | IJal : address -> instr
    (* termination *)
    | IHalt : instr.

    Definition eqb_op (op1 op2 : binop) :=
      match (op1,op2) with
        | (Addition,Addition) => true
        | (Subtraction,Subtraction) => true
        | (Multiplication,Multiplication) => true
        | (Equality,Equality) => true
        | (Leq,Leq) => true
        | (BitwiseOr,BitwiseOr) => true
        | (BitwiseAnd,BitwiseAnd) => true
        | (ShiftLeft,ShiftLeft) => true
        | _ => false
      end.

    Theorem  eqb_refl_op:
      forall op : binop,  eqb_op op op = true.
    Proof.
      intro op. unfold eqb_op. destruct op; reflexivity.
    Qed.

    Theorem eqb_eq_bop:
      forall op1 op2: binop, eqb_op op1 op2 = true <-> op1 = op2.
    Proof.
      split.
      - unfold eqb_op.
        destruct op1; destruct op2; intro H;
          try (reflexivity); try (inversion H).
      - intro H. rewrite H. apply eqb_refl_op.
    Qed.
        
    Definition eqb_instr (i1 i2 : instr) : bool :=
      match (i1,i2) with
      | (INop,INop) => true
      | (IConst v1 r1, IConst v2 r2) => (Z.eqb v1 v2)
                                          && (Register.eqb r1 r2)
      | (IMov r11 r12, IMov r21 r22) =>
        (Register.eqb r11 r21)
          && (Register.eqb r12 r22)
      | (IBinOp op1 r11 r12 r13, IBinOp op2 r21 r22 r23) =>
        (eqb_op op1 op2)
          && (Register.eqb r11 r21)
          && (Register.eqb r12 r22)
          && (Register.eqb r13 r23)
      | (ILoad r11 r12, ILoad r21 r22) =>
        (Register.eqb r11 r21)
          && (Register.eqb r12 r22)
      | (IStore r11 r12, IStore r21 r22) =>
        (Register.eqb r11 r21)
          && (Register.eqb r12 r22)
      | (IBnz r1 imm1, IBnz r2 imm2) =>
        (Register.eqb r1 r2)
          && (Z.eqb imm1 imm2)
      | (IJump r1, IJump r2) => (Register.eqb r1 r2)
      | (IJal a1, IJal a2) => (N.eqb a1 a2)
      | (IHalt, IHalt) => true
      | _ => false
      end.

    Theorem eqb_refl_instr:
      forall i : instr, eqb_instr i i = true.
    Proof.
      intro i. unfold eqb_instr.
      destruct i;
        try (reflexivity);
        try (apply N.eqb_refl);
        try (apply  andb_true_iff; split; apply Register.eqb_refl).
      - apply  andb_true_iff. split.
        + apply Z.eqb_refl.
        + apply Register.eqb_refl. 
      - repeat (apply  andb_true_iff; split);
          try (apply Register.eqb_refl).
        apply eqb_refl_op.
      - apply  andb_true_iff. split.
        + apply Register.eqb_refl.
        + apply Z.eqb_refl.
    Qed.
        
    Theorem eqb_eq_instr:
      forall i1 i2 : instr, eqb_instr i1 i2= true <-> i1 = i2.
    Proof.
      intros i1 i2. split.
      - unfold eqb_instr.
        destruct i1; destruct i2; intro H;
          try (reflexivity); try (inversion H);
            (* 2 register instructions *)
            try ( apply andb_true_iff in H; destruct H as [H' H''];
                  apply Register.eqb_eq in H'; rewrite H';
                  apply Register.eqb_eq in H''; rewrite H''; reflexivity);
            (* Const *)
            try ( apply andb_true_iff in H; destruct H as [H' H''];
                  apply Z.eqb_eq in H'; rewrite H';
                  apply Register.eqb_eq in H''; rewrite H''; reflexivity).
        (* BinOp *)
        + clear H1. apply andb_true_iff in H. destruct H as [H H1].
          apply andb_true_iff in H. destruct H as [H H2].
          apply andb_true_iff in H. destruct H as [H3 H4].
          apply eqb_eq_bop in H3. rewrite H3.
          apply Register.eqb_eq in H2. rewrite H2.
          apply Register.eqb_eq in H1. rewrite H1.
          apply Register.eqb_eq in H4. rewrite H4.
          reflexivity.
        (* Bnz *)
        + clear H1. apply andb_true_iff in H. destruct H as [H1 H2].
          apply Z.eqb_eq in H2. rewrite H2.
          apply Register.eqb_eq in H1; rewrite H1; reflexivity.
        (* Jump *)
        + apply Register.eqb_eq in H1; rewrite H1; reflexivity.
        + apply N.eqb_eq in H. rewrite H. reflexivity.
      - intro H. rewrite H. apply eqb_refl_instr.
        Qed.
            
          
    Theorem instr_eq_dec:
      forall i1 i2 : instr,  {i1 = i2} + {i1 <> i2}.
    Proof.
      repeat decide equality. Defined.
    
  End ISA.

  (* Type of a memory location *)
  Inductive word := 
  | Data : value -> word
  | Instruction : ISA.instr -> word.

  Definition eqb_word (w1 w2 : word) : bool :=
    match (w1,w2) with
    | (Data v1, Data v2) => Z.eqb v1 v2
    | (Instruction i1, Instruction i2) => ISA.eqb_instr i1 i2
    | _ => false
    end.

  Theorem eqb_refl_word:
    forall w : word, eqb_word w w = true.
  Proof.
    intro w. unfold eqb_word. destruct w.
    - apply Z.eqb_refl.
    - apply  ISA.eqb_refl_instr.
  Qed.

  Theorem eq_word_trans:
    forall (w1 w2 w3 : word), w1=w2 -> w2=w3 -> w1=w3.
  Proof.
    intros. destruct w1, w2, w3; inversion H; inversion H0; reflexivity.
  Qed.
    
  Theorem eqb_eq_word: forall (e e' : word),
      eqb_word e e' = true <-> e = e'.
  Proof.
    split.
    - unfold eqb_word. destruct e; destruct e'.
      + intro H. apply Z.eqb_eq in H. rewrite H. reflexivity.
      + intro H. inversion H.
      + intro H. inversion H.
      + intro H. apply ISA.eqb_eq_instr in H. rewrite H. reflexivity.
    - intro H. rewrite H. apply eqb_refl_word.
  Qed.
        
  (******************************************************
   * Memory Definitions
   ******************************************************)
  Module Memory.

    (* key: address, value: word at that address (data or code) *)
    Definition t := BinNatMap.t word.

    Definition get_word (mem : t) (ptr : address) : option word :=
      BinNatMap.find ptr mem.

    Definition get_value (mem : t) (ptr : address) : option value :=
      match get_word mem ptr with
      | Some (Data val) => Some val
      | _ => None
      end.

    Definition get_instr (mem : t) (ptr : address) : option RiscMachine.ISA.instr :=
      match get_word mem ptr with
      | Some (Instruction val) => Some val
      | _ => None
      end.
    
    
    Definition set_value (mem : t) (ptr : address) (val : value) : t :=
      BinNatMap.add ptr (Data val) mem.

    Definition set_instr (mem : t) (ptr : address) (i : ISA.instr) : t :=
      BinNatMap.add ptr (Instruction i) mem.


    Definition to_address (ptr:value) : address :=
      (* negatives are converted to zero *)
      Z.to_N ptr.

    (* returns an empty memory *)
    Definition empty : t := BinNatMap.empty word.

    (* returns all addresses that have been assigned a value *)
    Definition get_used_addresses (mem : t) :=
      BinNatMap.fold (fun key elt acc => key::acc) mem nil.

    Definition filter_used_addresses (mem : t) (filter : address -> bool) :=
      BinNatMap.fold (fun key elt acc =>
                        if (filter key)
                        then key::acc
                        else acc)
                     mem nil.
      
    Definition eqb (m1 m2 : t) : bool :=
      BinNatMap.equal eqb_word m1 m2.

    Definition Equal (m1 m2 : t) : Prop :=
      BinNatMap.Equal m1 m2.

    Theorem Equal_sym:
      forall (m1 m2 : t), Equal m1 m2 -> Equal m2 m1.
    Proof.
      intros m1 m2. apply (BinNatMapFacts.Equal_sym). 
    Qed.

    Theorem Equal_trans:
      forall (m1 m2 m3 : t),
        Equal m1 m2 -> Equal m2 m3 -> Equal m1 m3.
    Proof.
      unfold Equal.
      apply (BinNatMapFacts.Equal_trans).
    Qed.

    Theorem Equal_refl:
      forall (m : t), Equal m m.
    Proof.
      intro m. apply (BinNatMapFacts.Equal_refl). 
    Qed.
      
    Theorem eqb_refl:
      forall (m : t), eqb m m = true.
    Proof.
      unfold eqb. intros.
      apply BinNatMap.equal_1.
      apply BinNatMapFacts.Equal_Equivb.
      - apply eqb_eq_word.
      - apply BinNatMapFacts.Equal_refl.
    Qed.
    
    Lemma eqb_Equal: forall (m1 m2 : t),
        (eqb m1 m2) = true <->  BinNatMap.Equal m1 m2.
    Proof.
      split.
      - unfold eqb. intro H.
        apply BinNatMap.equal_2 in H.
        apply BinNatMapFacts.Equal_Equivb in H.
        + apply H.
        + apply eqb_eq_word.
      - intro H. unfold eqb.
        apply  BinNatMap.equal_1.
        apply BinNatMapFacts.Equal_Equivb.
        apply eqb_eq_word.
        apply H.
    Qed.

    Theorem get_word_Equal:
      forall (m1 m2 : t) (ptr : address),
        Equal m1 m2 -> (get_word m1 ptr) = (get_word m2 ptr).
    Proof.
      intros. unfold Equal in H. 
      unfold BinNatMap.Equal in H.
      unfold get_word. 
      apply H.
    Qed.

    Theorem get_value_Equal:
      forall (m1 m2 : t) (ptr : address),
        Equal m1 m2 -> (get_value m1 ptr) = (get_value m2 ptr).
    Proof.
      intros. unfold get_value. apply get_word_Equal with (m1:=m1) (m2:=m2) (ptr:=ptr) in H.
      rewrite H. reflexivity.
    Qed.

    Theorem  set_value_Equal:
      forall (m1 m2 : t) (ptr : address) (val : value),
        Equal m1 m2 -> Equal (set_value m1 ptr val) (set_value m2 ptr val).
    Proof.
      intros. unfold set_value.
      apply BinNatMapFacts.add_m.
      reflexivity. reflexivity. unfold Equal in H. apply H.
    Qed. 
      
  End Memory.

  (* evaluates the given binary operation *)
  Definition eval_binop (op : ISA.binop)
             (op1 : value) (op2 : value) : value :=
    match op with
    | ISA.Addition => op1 + op2
    | ISA.Subtraction => op1 - op2
    | ISA.Multiplication => op1 * op2
    | ISA.Equality => if Zeq_bool op1 op2 then 1 else 0
    | ISA.Leq => if Zle_bool op1 op2 then 1 else 0
    | ISA.BitwiseAnd => Z.land op1 op2
    | ISA.BitwiseOr => Z.lor op1 op2
    | ISA.ShiftLeft => Z.shiftl op1 op2
  end.
  
  Definition executing (mem : Memory.t) (pc : address) ( i : ISA.instr) : Prop :=
    match (Memory.get_word mem pc) with
    | Some (Instruction i') => i = i'
    |  _ => False
    end.

  Theorem executing_equal:
    forall (m1 m2 : Memory.t) (pc : address) ( i : ISA.instr),
      BinNatMap.Equal m1 m2 -> executing m1 pc i -> executing m2 pc i.
  Proof.
    unfold executing. unfold Memory.get_word. 
    simpl. intros.
    unfold BinNatMap.Equal in H. 
    rewrite H in H0. apply H0. 
  Qed.
  

  Definition inc_pc (a : pc) : pc := N.add a 1.

  Definition to_value (v : N) : value := Z.of_N v.
  
End RiscMachine.

Close Scope Z_scope.

(******************************************
 * SFIComponent Definition
 *******************************************)
Module SFIComponent.

  Definition id := N.

End SFIComponent.

(******************************************************
 * SFI specific definitions
 ******************************************************)
Module SFI.

  (* Number of bits used for offset within slot *)
  Definition OFFSET_BITS_NO : N := 12.

  (* Number of bits used for component *)
  Definition COMP_BITS_NO : N := 2.

  (* Definition COMPONENT_MASK : N := 2^CID_SIZE - 1. *)

  Definition CODE_DATA_BIT_MASK : N :=  N.shiftl 1 (OFFSET_BITS_NO + COMP_BITS_NO).

  (* Slot dimension *)
  Definition SLOT_SIZE : N := 2^OFFSET_BITS_NO.
  
  (* Maximum number of components, including the zero (special) component *)
  Definition COMP_MAX:N := 2^COMP_BITS_NO.

  Definition C_SFI (addr : RiscMachine.address) : SFIComponent.id  := 
    N.land (N.shiftr addr OFFSET_BITS_NO) (2^COMP_BITS_NO - 1).

  Definition ADDRESS_ALLIGN_BITS_NO : N := 4.

  Definition BASIC_BLOCK_SIZE : N := 16.

  Definition MONITOR_COMPONENT_ID : N := 0.

  Definition BLOCK_BITS_NO : N := 9.
  
  Definition AND_DATA_MASK : N :=
    N.lor
      (N.shiftl (2^BLOCK_BITS_NO -1) (OFFSET_BITS_NO+COMP_BITS_NO+1))
      (2^OFFSET_BITS_NO - 1).

  Definition AND_CODE_MASK : N :=
    N.lor
      (N.shiftl (2^BLOCK_BITS_NO-1) (OFFSET_BITS_NO+COMP_BITS_NO+1))
      (N.shiftl (2^(OFFSET_BITS_NO-ADDRESS_ALLIGN_BITS_NO) - 1) ADDRESS_ALLIGN_BITS_NO).

  Open Scope N_scope.
  
  (* Definition get_max_offset : N := 2^OFFSET_SIZE-1. *)

  (* Definition code_address_of (cid : SFIComponent.id) (bid off: N) : RiscMachine.address := *)
  (*   N.lor *)
  (*     (N.shiftl bid (COMP_BITS_NO+OFFSET_BITS_NO+1)) *)
  (*     (N.lor *)
  (*        (N.shiftl cid OFFSET_BITS_NO) *)
  (*        off).               *)

  (* Definition data_address_of (cid : SFIComponent.id) (bid off: N) : RiscMachine.address := *)
  (*   N.lor (code_address_of cid bid off) CODE_DATA_BIT_MASK. *)

  
  Definition address_of (cid : SFIComponent.id) (bid off: N) : RiscMachine.address :=
    N.lor
      (N.shiftl bid (COMP_BITS_NO+OFFSET_BITS_NO))
      (N.lor
         (N.shiftl cid OFFSET_BITS_NO)
         off).
  
  Close Scope N_scope.
  
  Definition is_same_component (addr1: RiscMachine.address)
             (addr2: RiscMachine.address) : Prop :=
    (C_SFI addr1) = (C_SFI addr2).
  
  Definition is_same_component_bool (addr1: RiscMachine.address)
             (addr2: RiscMachine.address) :=
    N.eqb (C_SFI addr1) (C_SFI addr2).

  Definition is_code_address  (addr : RiscMachine.address) : bool :=
    N.eqb (N.land addr CODE_DATA_BIT_MASK) N0.

  Definition is_data_address  (addr : RiscMachine.address) : bool :=
    negb (is_code_address addr).

  Definition or_data_mask (cid : SFIComponent.id) : N :=
    (N.shiftl (N.lor (N.shiftl 1%N COMP_BITS_NO) cid) OFFSET_BITS_NO).

  Definition or_code_mask (cid : SFIComponent.id) : N :=
    (N.shiftl cid OFFSET_BITS_NO).

  
  Module Allocator.
  
    Definition allocator_data_slot := 1%N.

    (* will allocate starting with 3, odd numbers *)
    (* 1 is reserved for dynamic memory allocation data *)
    Definition allocate_data_slots (n : nat) : (list N) :=
      (List.map (fun nn => (2 *(N.of_nat nn)  + 1)%N) (List.seq 1 n)).

    Definition allocate_code_slots (n : nat) : (list N) :=
      (List.map (fun n => ((N.of_nat n) * 2)%N)
                (List.seq 0 n)).
    
    Definition initial_allocator_value (n:nat) : RiscMachine.value :=
      Z.of_nat (n+1).

  End Allocator.

End SFI.

(******************************************************
 * Environment Definitions
 ******************************************************)
Module Env  <: UsualDecidableType.

  (* list of dimension COMP_MAX*)
  (* use the SFI component id as index to retrieve the intermediate
     level component id *)
  Definition CN := list Component.id.

  (* E is a partial map from addresses to procedure names.*)
  Definition E := list (RiscMachine.address*Procedure.id).

  Definition t := CN * E.

  Open Scope N_scope.
  Definition index2SFIid (i : nat) : SFIComponent.id :=
    (N.of_nat i) + 1.

  Definition SFIid2index (id : SFIComponent.id) : nat :=
    N.to_nat (id-1).
  Close Scope N_scope.
  
  Definition get_component_name_from_id (id : SFIComponent.id)
             (G : t): option Component.id :=
    ListUtil.get (SFIid2index id) (fst G).

  Definition get_procedure (addr : RiscMachine.address)
             (G : Env.t) : option Procedure.id :=
    ListUtil.get_by_key (N.eqb) addr (snd G).

  Definition eq_dec:
    forall g1 g2 : t,  {g1 = g2} + {g1 <> g2}.
  Proof.
    repeat decide equality. Defined.

  Include HasUsualEq <+ UsualIsEq.
  
End Env.


(******************************************************
 * Machine State Definitions
 ******************************************************)
Module MachineState.

  Definition t := RiscMachine.Memory.t * RiscMachine.pc * RiscMachine.RegisterFile.t.

  Definition getMemory (st : t) : RiscMachine.Memory.t := fst (fst st).

  Definition getPC (st : t) : RiscMachine.pc := snd (fst st).

  Definition getRegs (st : t) :  RiscMachine.RegisterFile.t := snd st.

  Definition empty : t := (RiscMachine.Memory.empty, RiscMachine.PC0,
                           RiscMachine.RegisterFile.reset_all).

  Definition eq (st1 st2 : t) : Prop :=
    let '(mem1,pc1,gen_regs1) := st1 in
    let '(mem2,pc2,gen_regs2) := st2 in
    (BinNatMap.Equal mem1 mem2) /\ (pc1 = pc2) /\
    (gen_regs1 = gen_regs2).
     
End MachineState.

(******************************************************
 * Program Definitions
 ******************************************************)
Record sfi_program :=
  {
    cn : Env.CN;
    e : Env.E;
    mem : RiscMachine.Memory.t;
    prog_interface : Program.interface
  }.


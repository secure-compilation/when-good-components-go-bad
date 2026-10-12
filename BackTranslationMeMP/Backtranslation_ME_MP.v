Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.SmallstepUB.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.BufferShape.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.RSC_ME_MP_Faithful.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section Replayer.

Variables (L P C : nat) (PI : Program.interface)
          (PB : NMap {fmap Block.id -> nat + seq value}) (t : trace).

Notation minstr := (@Merged.instr mt).
Notation mcode := (@Merged.code mt).

Definition rp_lab (cid j : nat) : nat := mk_body L cid j.

Definition rp_const (n : nat) (r : register) : minstr :=
  MrConst (@word_of_nat (imm_size mt) n) r.

Definition rp_small : nat := 2 ^ 14.

Definition rp_digits (N : nat) : seq nat :=
  [:: N %/ 2 ^ 28; (N %/ 2 ^ 21) %% 2 ^ 7; (N %/ 2 ^ 14) %% 2 ^ 7;
      (N %/ 2 ^ 7) %% 2 ^ 7; N %% 2 ^ 7].

Definition rp_load (N : nat) (r tmp : register) : seq minstr :=
  if N < rp_small then [:: rp_const N r]
  else match rp_digits N with
       | d :: ds =>
           rp_const d r
             :: flatten [seq [:: rp_const (2 ^ 7) tmp; MrBinop Mul r tmp r;
                                 rp_const d' tmp; MrBinop Add r tmp r] | d' <- ds]
       | [::] => [::]
       end.

Definition rp_word (z : Z) : nat := Z.to_nat (Z.modulo z (Z.pow 2 32)).

Definition rp_goto (cid j : nat) : seq minstr := [:: MrJal (rp_lab cid j)].

Definition rp_blocks : nat := size t + 2.

Definition rp_init (cid A j : nat) : seq minstr :=
  [:: rp_const A R_SP; MrLoad R_SP R_AUX1; MrBnz R_AUX1 (rp_lab cid j)]
  ++ rp_load rp_blocks R_ARG R_ONE
  ++ [:: MrMov (inl R_ARG) (inr R_SC_ARG1); MrJal alloc_label;
         MrMov (inr R_SC_RET) (inl R_AUX1); MrStore R_SP R_AUX1;
         rp_const 2 R_ARG; MrBinop Add R_AUX1 R_ARG R_ARG;
         rp_const 1 R_ONE; MrBinop Add R_AUX1 R_ONE R_SP; MrStore R_SP R_ARG;
         MrLabel (rp_lab cid j)].

Definition rp_push : seq minstr :=
  [:: rp_const 1 R_ONE; MrBinop Add R_AUX1 R_ONE R_SP; MrLoad R_SP R_ARG;
      MrStore R_ARG R_AUX2; MrBinop Add R_ARG R_ONE R_ARG; MrStore R_SP R_ARG].

Definition rp_test (cid k : nat) : seq minstr :=
  rp_load k R_ARG R_COM
  ++ [:: MrBinop Eq R_AUX2 R_ARG R_ARG; MrBnz R_ARG (rp_lab cid (4 + k))].

Definition rp_disp (cid A n : nat) : seq minstr :=
  [:: MrLabel (rp_lab cid 0); rp_const A R_SP; MrLoad R_SP R_AUX1; MrLoad R_AUX1 R_AUX2]
  ++ flatten [seq rp_test cid k | k <- iota 0 n]
  ++ [:: MrHalt].

Definition rp_case_body (cid : nat) (e : event) : seq minstr :=
  match e with
  | ECall _ P' z C' =>
      rp_load (rp_word z) R_COM R_ARG ++ MrJal (mk_entry L P C C' P') :: rp_goto cid 0
  | ERet _ z _ =>
      [:: rp_const 1 R_ONE; MrBinop Add R_AUX1 R_ONE R_SP; MrLoad R_SP R_ARG;
          MrBinop Minus R_ARG R_ONE R_ARG; MrStore R_SP R_ARG; MrLoad R_ARG R_RA]
      ++ rp_load (rp_word z) R_COM R_ARG ++ [:: MrJump R_RA]
  end.

Definition rp_case (cid : nat) (ke : nat * event) : seq minstr :=
  [:: MrLabel (rp_lab cid (4 + ke.1));
      rp_const 1 R_ONE; MrBinop Add R_AUX2 R_ONE R_AUX2; MrStore R_AUX1 R_AUX2]
  ++ rp_case_body cid ke.2.

Definition rp_events (cid : nat) : trace :=
  [seq e <- t | cur_comp_of_event e == cid].

Definition rp_tagged (cid : nat) (l : seq minstr) : mcode :=
  [seq (i, def_mem_tag cid true) | i <- l].

Definition rp_entry (cid p : nat) : mcode :=
  (MrLabel (mk_entry L P C cid p), Transitional.head_tag_gen PI cid p)
    :: rp_tagged cid (MrMov (inl R_RA) (inl R_AUX2) :: rp_goto cid 3).

Definition rp_block (cid : nat) : nat :=
  let bm := odflt emptym (PB cid) in
  odflt 0 (ohead [seq b <- domm bm | 0 < odflt 0 (omap bsize (bm b))]).

Definition rp_addr (cid : nat) : nat := bl_base PB cid (rp_block cid).

Definition rp_exports (cid : nat) : seq Procedure.id :=
  odflt fset0 (omap Component.export (PI cid)).

Definition rp_comp_code (cid : nat) : mcode :=
  let es := rp_events cid in
  let A := rp_addr cid in
  (if cid == Component.main then rp_tagged cid (rp_init cid A 1 ++ rp_goto cid 0) else [::])
  ++ flatten [seq rp_entry cid p | p <- rp_exports cid]
  ++ rp_tagged cid (MrLabel (rp_lab cid 3) :: rp_init cid A 2 ++ rp_push ++ rp_goto cid 0
                    ++ rp_disp cid A (size es)
                    ++ flatten [seq rp_case cid ke | ke <- zip (iota 0 (size es)) es]
                    ++ [:: MrHalt]).

Definition rp_program (I : Program.interface)
    (Bs : NMap {fmap Block.id -> nat + seq value}) : program :=
  {| prog_interface := I;
     code := flatten [seq rp_comp_code cid | cid <- domm I];
     prog_buffers := mapm (mapm (fun x => inl (bsize x))) Bs;
     prog_main := Component.main \in domm I |}.

End Replayer.

Definition bt_side (L P C : nat) (p c : program) (t : trace) (q : program) : program :=
  rp_program L P C (unionm (prog_interface p) (prog_interface c))
             (unionm (prog_buffers p) (prog_buffers c)) t
             (prog_interface q) (prog_buffers q).

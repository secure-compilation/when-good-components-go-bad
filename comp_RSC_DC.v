Require Import Classical.
Require Import Classical_Pred_Type.
Require Import Setoid.

(*********************************************************)
(* Some useful Lemma to handle classical facts *)
Lemma dne : forall P : Prop, P <-> ~ ~ P.
Proof.
 intros P. split.
 - intros p np. apply (np p).
 - apply (NNPP P).
Qed.

Lemma imp_eqiv : forall P Q : Prop,
    (P -> Q) <-> ~P \/ Q.
Proof.
 intros P Q. split.
- apply imply_to_or.
- intros H p. destruct H.
  + exfalso. apply (H p). + apply H.
Qed.

Lemma not_imp : forall P Q : Prop,
    ~(P -> Q) <-> P /\ ~ Q.
Proof.
  intros P Q. split.
  - apply imply_to_and.
  - intros [p nq] i. apply (nq (i p)).
Qed.

Lemma contra : forall P Q : Prop,
    (P -> Q) <-> (~Q -> ~P).
Proof.
  intros P Q. split.
  - intros H nq p. apply (nq (H p)).
  - intros H p. rewrite -> (dne Q).
    intros nq. apply (H nq p).
Qed.

Lemma de_morgan1 : forall P Q : Prop,
    ~ (P /\ Q) <-> ~P \/ ~Q.
Proof.
  intros P Q. split.
  - apply not_and_or.
  - intros [] [p q]. apply (H p). apply (H q).
Qed.

Lemma de_morgan2 : forall P Q : Prop,
    ~ (P \/ Q) <-> ~P /\ ~Q.
Proof.
  intros P Q. split.
  - apply not_or_and.
  - intros [np nq] []. apply np. assumption. apply (nq H).
Qed.

Lemma not_forall_ex_not : forall (U : Type) (P : U -> Prop),
    ~ (forall n : U, P n) <-> exists n : U, ~ P n.
Proof.
  intros U P. split.
  - apply (not_all_ex_not U P).
  - apply (ex_not_not_all U P).
Qed.

Lemma not_ex_forall_not : forall (U :Type) (P : U -> Prop),
    (~ exists n : U, P n) <-> forall n : U, ~ P n.
Proof.
 intros U P. split.
 - apply not_ex_all_not.
 - intros H [n p]. apply (H n p).
Qed.

Lemma and_implies_or : forall P Q : Prop, P /\ Q -> P \/ Q.
Proof.
  intros P Q [p q]. apply (or_introl p).
Qed.


(*********************************************************)


Require Import Events.
Require Import Behaviors.

(*********************************************************)

Definition prop := program_behavior -> Prop.
Variable prg prg' ctx ctx' : Set.

Variable plug : prg -> ctx -> prg.
Variable plug': prg' -> ctx' -> prg'.
Variable sem : prg -> prop.
Variable sem': prg' -> prop.
Variable compile : prg -> prg'.

(* program P *satisfies* property π *)
Definition sat (P:prg) (π:prop) : Prop :=
  forall b, sem P b -> π b.

Definition sat' (P':prg') (π:prop) : Prop :=
  forall b, sem' P' b -> π b.

(* program P *robustly satisfies* property π *)
Definition rsat (P:prg) (π:prop) : Prop :=
  forall C, sat (plug P C) π.

Definition rsat' (P':prg') (π:prop) : Prop :=
  forall C, sat' (plug' P' C) π.

(* robust preservation *)
Definition RP (P : prg) (pi : prop) : Prop :=
  rsat P pi -> rsat' (compile P) pi.

Lemma neg_rsat : forall P π,
       ~ rsat P π <->
       (exists C t,
           sem (plug P C) t /\ ~ π t).
Proof.
  unfold rsat. unfold sat. split.
  - intros r. rewrite not_forall_ex_not in r.
    destruct r as [C r]. rewrite not_forall_ex_not in r.
    destruct r as [t r]. exists C,t. rewrite not_imp in r.
    assumption.
  - intros [C [t r]]. rewrite not_forall_ex_not.
    exists C. rewrite not_forall_ex_not. exists t.
    rewrite not_imp. assumption.
Qed.

Lemma neg_rsat' : forall P π,
       ~ rsat' P π <->
       (exists C t,
           sem' (plug' P C) t /\ ~ π t).
Proof.
   unfold rsat'. unfold sat'. split.
  - intros r. rewrite not_forall_ex_not in r.
    destruct r as [C r]. rewrite not_forall_ex_not in r.
    destruct r as [t r]. exists C,t. rewrite not_imp in r.
    assumption.
  - intros [C [t r]]. rewrite not_forall_ex_not.
    exists C. rewrite not_forall_ex_not. exists t.
    rewrite not_imp. assumption.
Qed.

(* contrapositive form of RP, classically equivalent *)
Lemma contra_RP (P : prg) (pi : prop) : RP P pi <->
     ((exists C' t',
       sem' (plug' (compile P) C') t' /\ ~ pi t') ->
      (exists C t,
       sem (plug P C) t /\ ~ pi t)).
Proof.
  unfold RP. split.
  - intros H. rewrite contra in H.
    rewrite neg_rsat in H. rewrite neg_rsat' in H.
    assumption.
  - intros H. rewrite contra. rewrite neg_rsat. rewrite neg_rsat'.
    assumption.
Qed.

(*********************************************************)
(*  foall P : prg,                                       *)
(*   RC_dc P  <-> Robust Preservation of Z_p             *)
(*********************************************************)

Variable undef : prg -> trace -> trace. (* undef P m = m; (Undef P) *)

Axiom undef_no_extension : forall P b m,
    behavior_prefix (undef P m) b -> b = Goes_wrong (undef P m).

Axiom no_nested : forall P m,
    undef P (undef P m) = undef P m.

Axiom undef_longer : forall P m,
    trace_prefix m (undef P m).

Lemma pref_undef_pref : forall P m m',
    trace_prefix m (undef P m') ->
    (m = undef P m') \/ (trace_prefix m m').
Admitted.

Fixpoint snoc m e : trace :=
  match m with
  | nil => cons e nil 
  | cons x xs => cons x (snoc xs e)
  end.
        
Definition u_prefix P b m: Prop :=
  exists mb,  trace_prefix mb m  /\
          b = Goes_wrong (undef P mb).

          
Lemma trace_prefix_trans : forall m1 m2 m,
    trace_prefix m1 m2 -> trace_prefix m2 m ->
    trace_prefix m1 m.
Admitted.

Lemma trace_prefix_ref : forall m, trace_prefix m m.
Admitted.

Lemma behavior_prefix_pseudo_trans : forall m1 m2 b,
    behavior_prefix m1 b -> trace_prefix m2 m1 ->
    behavior_prefix m2 b.
Admitted.

Lemma u_prefix_pseudo_trans: forall P t m1 m2,
    u_prefix P t m1 -> trace_prefix m1 m2 ->
    u_prefix P t m2.
Proof. Admitted.

Lemma same_extension : forall m1 m2 t,
    behavior_prefix m1 t -> behavior_prefix m2 t ->
    (trace_prefix m1 m2 \/ trace_prefix m2 m1).
Admitted. 

 
Definition RSC_dc (P : prg) : Prop :=
  forall C' t, sem' (plug' (compile P) C') t ->
   (forall m, behavior_prefix m t ->  
      exists C t', sem (plug P C) t' /\
              (behavior_prefix m t' \/ u_prefix P t' m)).

Definition Z_class P π : Prop :=
  forall t,  ~ π t ->
   (exists m, behavior_prefix m t /\
         forall t', (behavior_prefix m t' \/ u_prefix P t' m) -> ~ π t').

Theorem RSC_dc_RZP : forall P : prg,
    RSC_dc P -> (forall π, Z_class P π -> RP P π).
Proof.
  intros P r π z. rewrite contra_RP. intros [C' [t [h0 h1]]].
  destruct (z t h1) as [m [pmt H]]. clear z.
  destruct (r C' t h0 m pmt) as [C [ t' [k0 k1]]]. clear r.
  exists C, t'. split. - assumption. - apply (H t' k1).
Qed.

Theorem RZP_RSC_dc : forall P : prg,
    (forall π, Z_class P π -> RP P π) -> RSC_dc P.
Proof.
  unfold RSC_dc. intros P rz C' t H0 m pmt.
  assert (K : Z_class P (fun b => ~ (behavior_prefix m b \/ u_prefix P b m))).
  { unfold Z_class. intros t0 Ht0. rewrite <- dne in Ht0. 
    destruct Ht0 as [use_m | Ht0].
    + exists m. split. auto. intros t' Ht'. now rewrite dne in Ht'.
    + destruct Ht0 as [m0 [Hpref Hb]].
      exists (undef P m0). split; auto. 
      ++ exists (Goes_wrong nil). simpl.
          now rewrite E0_right. (*TODO : Lemmas for this *)
          intros t' [H | [mb [H1 H2]]]; rewrite <- dne.
          +++ apply undef_no_extension in H. subst.
          +++ right. now exists m0. 
      ++ right. assert ( mb = (undef P m0) \/ trace_prefix mb m0)
                by now apply (pref_undef_pref P mb m0).
         destruct H as [K1 | K2].
         +++ exists m0. subst. split; try now auto. now rewrite no_nested.
         +++ exists mb. split; try now auto.
             now apply (trace_prefix_trans mb m0 m).                            
   } 
  assert (T : ~ (fun b => ~ (behavior_prefix m b \/ u_prefix P b m)) t).
  { rewrite <- dne. left. assumption. }
  specialize (rz (fun b => ~ (behavior_prefix m b \/ u_prefix P b m)) K).
  rewrite contra_RP in rz. destruct rz as [C [t' [k0 k1]]]. exists C',t. split. assumption.
  rewrite <- dne. left. assumption. exists C,t'.
  split. assumption. rewrite <- dne in k1. assumption.
Qed.

Corollary pointwise_equiv' : forall P : prg,
    RSC_dc P <-> (forall pi : prop, Z_class P pi -> RP P pi).
Proof.
  intros P. split.
  - apply RSC_dc_RZP.
  - apply RZP_RSC_dc.
Qed.

Corollary main_thm' :
    (forall P, RSC_dc P) <-> (forall P pi, Z_class P pi -> RP P pi).
   (* ^^^^^^^^^^^^^^^^ *)    
   (*      RSC^DC      *)    
Proof.
  split. - intros H P. now apply RSC_dc_RZP.
         - intros H P. apply RZP_RSC_dc. now apply H.
Qed.


(*********************************************************)
(*  Relation between Z_p and Safety                      *)
(*********************************************************)

Definition Safety (π : prop) : Prop :=
  forall t, ~ π t -> exists m, behavior_prefix m t /\
        (forall t', behavior_prefix m t' -> ~ π t').

(* Z_class is a sublclass of safety *)
Lemma Z_p_Safety : forall (P : prg) (pi : prop),
    Z_class P pi -> Safety pi.
Proof.
  unfold Safety. intros P pi Z t nt.
  destruct (Z t nt) as [m [pmt H]]. clear Z.
  exists m. split; now auto.
Qed.

(* Class of property closed under refinement
   (undef due to program P)
 *)
Definition ref_cl (P : prg) (π : prop) : Prop :=
  forall t, π t ->
       forall t', (exists m', behavior_prefix m' t' /\
                      u_prefix P t m') -> π t'.

(* classically equivalent formulation for ref_cl *)
Lemma ref_cl' : forall (P : prg) (π : prop),
    ref_cl P π <->
    (forall t', ~ π t' ->
          forall t, (exists m', behavior_prefix m' t' /\
                  u_prefix P t m') -> ~ π t).
Proof.
  intros P π. split.
  - intros r t' nt' t [m' [Hm' Hu']] pit.
    apply nt'. apply (r t pit t'). now exists m'.
  - unfold ref_cl. intros r t pit t' utt'. apply NNPP.
    intros npi'. apply ((r t' npi' t utt') pit).
Qed.

Lemma U_general : forall P t1 t2,
    (exists m2, behavior_prefix m2 t2 /\ u_prefix P t1 m2) ->
    (forall m, behavior_prefix m t2 ->
               (behavior_prefix m t1 \/ u_prefix P t1 m)).
Proof.
  intros P t1 t2 [m2 [H2 Hu]] m pm2. 
  destruct Hu as [mm [H0 H1]].
  assert (foo : trace_prefix m mm \/ trace_prefix mm m).
  { apply (same_extension m mm t2); try now auto.
    now apply (behavior_prefix_pseudo_trans m2 mm t2). }
  destruct foo as [k0 | k1].    
  + left. assert (trace_prefix m (undef P mm)).
    { apply (trace_prefix_trans m mm (undef P mm)); try now auto.
      now apply (undef_longer P mm). }
    unfold behavior_prefix.
    destruct H as [l Hl]. exists (Goes_wrong l).
    simpl. now rewrite Hl in *. 
  + right. unfold u_prefix.
    now exists mm.
Qed. 

Lemma Z_p_equivalent : forall (P : prg) (π : prop),
    Z_class P π <-> Safety π /\ ref_cl P π.
Proof.
  intros P π. split.
  - intros z. split.
    + now apply (Z_p_Safety P). 
    + rewrite ref_cl'. intros t' nt' t utt'.
      destruct (z t' nt') as [m [pmt zz]].
      assert (behavior_prefix m t \/ u_prefix P t m) as use_me by
      apply  (U_general P t t' utt' m pmt).
      apply (zz t use_me).      
  -  intros [s r]. unfold Z_class.
     intros t nt. destruct (s t nt) as [m [pmt H]].
     exists m. split; try now auto.
     intros t' [k0 | k1].
     apply (H t' k0).
     assert (use_me : exists m', behavior_prefix m' t /\ u_prefix P t' m').
     { unfold u_prefix. destruct k1 as [m0 [p0 u0]].
       exists m0. split; try now auto. 
       now apply (behavior_prefix_pseudo_trans m m0 t).
       exists m0. split; try now auto.
       now apply trace_prefix_ref. }      
     rewrite ref_cl' in r. apply (r t nt t' use_me).
Qed.

Lemma easy_lemma0 :
  (forall P π, Z_class P π -> RP P π) <->
  (forall P π, (Safety π /\ ref_cl P π) -> RP P π).
Proof.
  split.
  - intros L P π H. rewrite <- (Z_p_equivalent P π) in H.
    now apply (L P).
  - intros R P π Z. rewrite (Z_p_equivalent P π) in Z.
    now apply (R P π).
Qed.

Lemma easy_lemma1 : forall P : prg,
  (forall  π, Z_class P π -> RP P π) <->
  (forall  π, (Safety π /\ ref_cl P π) -> RP P π).
Proof.
  intros P. split.
  - intros L π H. rewrite <- (Z_p_equivalent P π) in H.
    apply (L π H).
  - intros R π H. rewrite (Z_p_equivalent P π) in H.    
    apply (R π H).
Qed.

(* theorem in the paper *)
Corollary main_thm : 
  (forall P : prg, RSC_dc P) <->
  (forall P π, (Safety π /\ ref_cl P π) -> RP P π).
Proof. rewrite <- easy_lemma0. apply main_thm'. Qed.

Corollary pointwise_equiv : forall P : prg,
    RSC_dc P <->
    (forall π : prop, (Safety π /\ ref_cl P π) -> RP P π).
Proof.
  intros P.
  rewrite <- (easy_lemma1 P). apply pointwise_equiv'.
Qed.

(*********************************************************)
(*  extracting a Z_class property from a Safety one      *)
(*********************************************************)

(* starting from a safety property π we define the following *)
Definition z_plus (π : prop) (S:Safety π) (P : prg) : prop :=
  fun t =>    π t /\
           forall t', (exists m', behavior_prefix m' t' /\
                    u_prefix P t m') -> π t'.

(* z_plus is a subproperty of π *)
Lemma sub : forall (π : prop) (S : Safety π)
                   (P : prg) (b : program_behavior),
                    (z_plus π S P b) -> π b.
Proof. intros π S P b [h0 h1]; assumption. Qed.

Lemma sub' : forall (π : prop) (S : Safety π)
                    (P : prg) (b : program_behavior),
                     ~ π b -> ~ (z_plus π S P b).
Proof. intros π S P b. rewrite <- contra.  
       apply (sub π S P).
Qed.

(* z_plus is in Z_class *)
Lemma extraction_lemma :  forall (π : prop) (P : prg)
                                 (s : Safety π),
                           Z_class P (z_plus π s P).
Proof.
  intros π P s. rewrite Z_p_equivalent. split.
  - unfold Safety. intros t nt.
    unfold z_plus in nt. rewrite de_morgan1 in nt.
    destruct nt as [k0 | k1].
    + destruct (s t k0) as [m [a1 a2]].
      exists m. split; try now auto. 
      intros t' H. specialize (a2 t' H).
      apply (sub' π s P t' a2).
    +admit.
  - admit.
Admitted.


(* z_plus is the biggest property in Z_p that is included in π *)
Lemma maximality_lemma : forall (P : prg) (π phi : prop) (S : Safety π)
                                (Zphi : Z_class P phi)
                                (H: forall b, phi b -> π b),

    forall b, phi b -> (z_plus π S P) b.
Proof.
  intros P π phi S Zphi H b phib.
  unfold z_plus. split.
  - apply (H b phib).
  - intros t ubt. rewrite dne. intros nπt.
    assert (nphit : ~ phi t).
    { intros phit. apply (nπt (H t phit)). }
    specialize (Zphi t nphit).
    destruct Zphi as [m [pmt K]].
    assert (use_me : behavior_prefix m b \/ u_prefix P b m).
    { apply (U_general P b t ubt m pmt). }
    apply ((K b use_me) phib).
Qed.


(*********************************************************)
(*  building a Z_class property on a Safety one          *)
(*********************************************************)

(* starting from a safety property π we define the following *)
Definition z_minus (P : prg) (π : prop) : prop :=
  fun b =>
    π b \/ (exists t m, behavior_prefix m b /\ π t /\
                  (u_prefix P t m \/ behavior_prefix m t)). 

(* π is included in z_minus *)
Lemma sub_minus : forall (P : prg) (π : prop) (b : program_behavior),
                  π b -> (z_minus P π) b.
Proof. intros P π b H.  unfold z_minus. left. apply H. Qed.    

(* z_minus is in Z_p *)
Lemma growth_lemma : forall (P : prg) (π : prop) (S : Safety π),
                     Z_class P (z_minus P π).
Proof. Admitted.

(* and is the smallest property in Z_p including π *)
Lemma minimality_lemma : forall (P : prg) (π phi : prop) (S: Safety π) (Z: Z_class P phi),
                                (forall b, π b -> phi b) ->
                                (forall b', z_minus P π b' -> phi b').
Proof. Admitted.
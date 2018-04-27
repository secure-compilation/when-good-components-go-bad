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
(* SNOC                                                  *)
(*********************************************************)
Fixpoint snoc m e : trace :=
  match m with
  | nil => cons e nil 
  | cons x xs => cons x (snoc xs e)
  end.
   
Lemma snoc_lemma : forall m,
    m = nil \/ (exists e m', m = snoc m' e).
Proof.
  induction m.
  + now left.
  + right. destruct IHm as [Knil | [e [m' K]]];
           [exists a, nil | exists e, (cons a m')]; now subst. 
Qed.


Lemma snoc_app : forall m e,
    snoc m e = m ** (cons e nil).
Proof.
  intros m e. induction m; try now auto.
  + simpl. now rewrite IHm.
Qed.

Lemma snoc_append : forall m1 m2 e,
    m1 ** (snoc m2 e) = m1 ** m2 ** (cons e nil).
Proof.
  intros m1 m2 e. induction m2; try now auto.
  + simpl. now rewrite (snoc_app m2 e).
Qed.

Lemma foo_lemma : forall m e, snoc m e = nil -> False.
Proof.
  intros m e H. destruct m; now inversion H.
Qed. 

Lemma snoc_eq : forall m1 m2 e1 e2,
    snoc m1 e1 = snoc m2 e2 ->
    m1 = m2 /\ e1 = e2.
Proof.
  intros m1. induction m1; intros m2 e1 e2 H.
  + destruct m2; inversion H; try now auto. 
    exfalso. symmetry in H2. now apply (foo_lemma m2 e2).
  + destruct m2; inversion H. 
    exfalso. symmetry in H2. now apply (foo_lemma m1 e1).
    specialize (IHm1 m2 e1 e2 H2).
    destruct IHm1 as [k1 k2]. rewrite k1. now auto.
Qed. 
  
Lemma same_length : forall m1 m2 e1 e2,
    m1 ** (cons e1 nil) = m2 ** (cons e2 nil) ->
    m1 = m2 /\ e1 = e2.
Proof.
  intros m1 m2 e1 e2 H.
  rewrite <- (snoc_app m1 e1) in H. rewrite <- (snoc_app m2 e2) in H.
  now apply snoc_eq.
Qed.

Lemma snoc_pref : forall m m1 e1,
    trace_prefix m (snoc m1 e1) ->
    m = snoc m1 e1 \/ trace_prefix m m1.
Proof.
  intros m m1 e1 [[] Hb]. 
  + rewrite E0_right in Hb. now left.
  + specialize (snoc_lemma (cons e l)).
    intros [H | [e' [l' H]]]; rewrite H in Hb. 
    ++ rewrite E0_right in Hb. now left.
    ++ right. exists l'. rewrite snoc_append in Hb.
       rewrite snoc_app in Hb.
       rewrite <- Eapp_assoc in Hb.
       apply (same_length m1 (m ** l') e1 e') in Hb. 
       now auto.
Qed. 

(*********************************************************)
(*  foall P : prg,                                       *)
(*   RC_dc P  <-> Robust Preservation of Z_p             *)
(*********************************************************)

Variable undef : prg -> event.

Axiom undef_no_extension_behavior : forall P b m,
    behavior_prefix (snoc m (undef P)) b -> b = Goes_wrong (snoc m (undef P)).

Lemma undef_no_extension_trace : forall P t m,
    trace_prefix (snoc m (undef P)) t -> t = (snoc m (undef P)).
Proof.
  intros P t m [t' Ht'].
  specialize (undef_no_extension_behavior P (Goes_wrong t) m).
  intros H. assert (behavior_prefix (snoc m (undef P)) (Goes_wrong t)).
  { exists (Goes_wrong t').  simpl. subst. now auto. }
  specialize (H H0). now inversion H.
Qed.

Lemma no_nested : forall P m,
    snoc (snoc m (undef P)) (undef P) = snoc m (undef P).
Proof.
  intros P m. apply (undef_no_extension_trace P (snoc (snoc m (undef P)) (undef P)) m).
  exists (cons (undef P) nil). now rewrite <- (snoc_app (snoc m (undef P))).
Qed. 

Lemma undef_longer : forall P m,
    trace_prefix m (snoc m (undef P)).
Proof.
  intros P m. exists (cons (undef P) nil).
  now rewrite snoc_app.
Qed. 

Lemma pref_undef_pref : forall P m m',
    trace_prefix m  (snoc m' (undef P)) ->
    (m = snoc m' (undef P)) \/ (trace_prefix m m').
Proof.
  intros P m m' H. now apply (snoc_pref m m' (undef P)).
Qed.                   
        
Definition u_prefix P b m: Prop :=
  exists mb,  trace_prefix mb m  /\
          b = Goes_wrong (snoc mb (undef P)).
          
Lemma trace_prefix_trans : forall m1 m2 m,
    trace_prefix m1 m2 -> trace_prefix m2 m ->
    trace_prefix m1 m.
Proof.
  intros m1 m2 m [b1 Hb1] [b2 Hb2]. rewrite Hb1 in Hb2.
  rewrite Eapp_assoc in Hb2. now exists (b1 ** b2).
Qed. 

Lemma trace_prefix_ref : forall m, trace_prefix m m.
Proof. intros m. exists nil. now rewrite E0_right. Qed. 

Lemma behavior_prefix_pseudo_trans : forall m1 m2 b,
    behavior_prefix m1 b -> trace_prefix m2 m1 ->
    behavior_prefix m2 b.
Proof.
  intros m1 m2 b [t1 Ht1] [t2 Ht2].
  unfold behavior_prefix. subst.
  exists (behavior_app t2 t1). now apply behavior_app_assoc.
Qed. 

Lemma u_prefix_pseudo_trans: forall P t m1 m2,
    u_prefix P t m1 -> trace_prefix m1 m2 ->
    u_prefix P t m2.
Proof.
  intros P t m1 m2 [ub [Hub1 Hub2]] [t1 Ht1].
  unfold u_prefix. exists ub.
  destruct Hub1 as [tt1 Htt1]. rewrite Htt1 in Ht1.
  rewrite Eapp_assoc in Ht1. split; try now auto.
  now exists (tt1 ** t1).
Qed. 

Lemma same_extension_trace : forall m1 m2 t,
    trace_prefix m1 t -> trace_prefix m2 t ->
    (trace_prefix m1 m2 \/ trace_prefix m2 m1).
Proof.
  intros m1. induction m1; intros m2 t [b1 Hb1] [b2 Hb2]; rewrite Hb1 in Hb2.
  + left. exists m2. now rewrite E0_left. 
  + destruct m2.
    ++ right. exists (cons a m1). now rewrite E0_left. inversion Hb2. subst.
       destruct (IHm1 m2 (m1 ** b1)) as [[l Hl] | [l Hl]].
       now exists b1. now exists b2.
       +++ left. exists l. simpl. now rewrite Hl.
       +++ right; exists l. simpl. now rewrite Hl.
Qed. 
    
Lemma same_extension_stream : forall m1 m2 t,
    traceinf_prefix m1 t -> traceinf_prefix m2 t ->
    (trace_prefix m1 m2 \/ trace_prefix m2 m1).
Proof.
  intros m1. induction m1; intros m2 t [b1 Hb1] [b2 Hb2]; rewrite Hb1 in Hb2.
  + left. exists m2. now rewrite E0_left. 
  + destruct m2.
    ++ right. exists (cons a m1). now rewrite E0_left. inversion Hb2. subst.
       destruct (IHm1 m2 (m1 *** b1)) as [[l Hl] | [l Hl]].
       now exists b1. now exists b2.
       +++ left. exists l. simpl. now rewrite Hl.
       +++ right; exists l. simpl. now rewrite Hl.
Qed.

Lemma same_extension : forall m1 m2 t,
    behavior_prefix m1 t -> behavior_prefix m2 t ->
    (trace_prefix m1 m2 \/ trace_prefix m2 m1).
Proof.
  intros m1 m2 [] [[] Hb1] [[] Hb2]; try (inversion Hb1; inversion Hb2);
    rewrite H0 in H1.
    + assert (trace_prefix m1 (m1 ** t0)) by now exists t0.
      assert (trace_prefix m2 (m1 ** t0)) by now exists t1.
      now apply (same_extension_trace m1 m2 (m1 ** t0)).
    + assert (trace_prefix m1 (m1 ** t0)) by now exists t0.
      assert (trace_prefix m2 (m1 ** t0)) by now exists t1.
      now apply (same_extension_trace m1 m2 (m1 ** t0)).  
    + assert (traceinf_prefix m1 (m1 *** t0)) by now exists t0.
      assert (traceinf_prefix m2 (m1 *** t0)) by now exists t1.
      now apply (same_extension_stream m1 m2 (m1 *** t0)).
    + assert (trace_prefix m1 (m1 ** t0)) by now exists t0.
      assert (trace_prefix m2 (m1 ** t0)) by now exists t1.
      now apply (same_extension_trace m1 m2 (m1 ** t0)). 
Qed.
       
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
      exists (snoc m0 (undef P)). split; auto. 
      ++ exists (Goes_wrong nil). simpl.
          now rewrite E0_right. (*TODO : Lemmas for this *)
          intros t' [H | [mb [H1 H2]]]; rewrite <- dne.
          +++ apply undef_no_extension_behavior in H. subst.
          +++ right. now exists m0. 
      ++ right. assert ( mb = (snoc m0 (undef P)) \/ trace_prefix mb m0)
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
  + left. assert (trace_prefix m (snoc mm (undef P))).
    { apply (trace_prefix_trans m mm (snoc mm (undef P))); try now auto.
      now apply (undef_longer P mm). }
    destruct H as [l Hl]. exists (Goes_wrong l).
    simpl. now rewrite Hl in *. 
  + right. now exists mm.
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

Definition u_prefix_b P t1 t2 : Prop :=
  exists m2, behavior_prefix m2 t2 /\ u_prefix P t1 m2.

(* starting from a safety property π we define the following *)
Definition z_plus (π : prop) (S:Safety π) (P : prg) : prop :=
  fun t =>  π t /\
           forall t', u_prefix_b P t t' -> π t'.

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
  intros π P s. unfold Z_class. intros t H.
  unfold z_plus in *. rewrite de_morgan1 in H.
  destruct H as [K | K].
  + destruct (s t K) as [m [Hm1 Hm2]]. 
    exists m. split; try now auto.
    intros t' [Hpref | Hundef]; rewrite de_morgan1.
    ++ left. now apply (Hm2 t').
    ++ right. intros Hf. apply K.
       apply (Hf t). unfold u_prefix_b.
       now exists m.
  + rewrite not_forall_ex_not in K. destruct K as [t' Ht'].
    rewrite not_imp in Ht'. destruct Ht' as [[b [Hb1 [m [H1 H2]]]] H].
    destruct (s t' H) as [m' [Hm' HHm']].
    exists (snoc m (undef P)). split.
    ++ unfold behavior_prefix. exists (Goes_wrong nil). simpl. now rewrite E0_right.
    ++ intros t'0 [Hpref | Hundef]; rewrite de_morgan1.
       +++ apply undef_no_extension_behavior in Hpref.
           apply (behavior_prefix_pseudo_trans b m t' Hb1) in H1.
           assert (trace_prefix m m' \/ trace_prefix m' m)
             by now apply (same_extension m m' t').
           destruct H0.
           *  right. intros ff. apply H. apply ff.
             unfold u_prefix_b. exists m. split; try now auto.
             unfold u_prefix. exists m. split; try now auto.
             now apply trace_prefix_ref. 
           * left. subst. apply HHm'. destruct H0 as [l Hl].
             rewrite Hl. exists (Goes_wrong (snoc l (undef P))).
             simpl. rewrite (snoc_append m' l (undef P)).
             rewrite (snoc_app (m' ** l) (undef P)).
             now rewrite Eapp_assoc.
        +++ destruct Hundef as [b0 [Hb0 Hb00]].  
            assert (b0 = (snoc m (undef P)) \/ trace_prefix b0 m) by
                now apply (pref_undef_pref P b0 m).
            destruct H0 as [K | K].
           * rewrite K in Hb00. rewrite no_nested in Hb00. rewrite <- H2 in Hb00.
             rewrite Hb00 in *. right. intros Hf. apply H. apply Hf.
             exists m. split. 
             ** now apply (behavior_prefix_pseudo_trans b m t'). 
             ** exists m. split; try now auto. now apply trace_prefix_ref.
           * right. intros ff. apply H. apply ff.
             unfold u_prefix_b. exists b0. split.
             apply (behavior_prefix_pseudo_trans b m t' Hb1) in H1. 
             now apply (behavior_prefix_pseudo_trans m b0 t').
             exists b0. split; try now auto. now apply trace_prefix_ref. 
Qed.      


(* z_plus is the biggest property in Z_p that is included in π *)
Lemma maximality_lemma : forall (P : prg) (π phi : prop) (S : Safety π)
                                (Zphi : Z_class P phi)
                                (H: forall b, phi b -> π b),

    forall b, phi b -> (z_plus π S P) b.
Proof.
  intros P π phi S Zphi H b phib.
  unfold z_plus. split.
  - apply (H b phib).
  - intros t [m [Hpref Hu]]. rewrite dne. intros nπt.
    assert (nphit : ~ phi t).
    { intros phit. apply (nπt (H t phit)). }
    specialize (Zphi t nphit).
    destruct Zphi as [m' [pmt K]].
    assert (use_me : behavior_prefix m' b \/ u_prefix P b m').
    { apply (U_general P b t); try now auto. now exists m.  }
    apply ((K b use_me) phib).
Qed.


(*********************************************************)
(*  building a Z_class property on a Safety one          *)
(*********************************************************)

(* starting from a safety property π we define the following *)
Definition z_minus (P : prg) (π : prop) : prop :=
  fun b =>
    π b \/ (exists t,  π t /\ (u_prefix_b P t b)). 

(* π is included in z_minus *)
Lemma sub_minus : forall (P : prg) (π : prop) (b : program_behavior),
                  π b -> (z_minus P π) b.
Proof. intros P π b H.  unfold z_minus. left. apply H. Qed.    


Lemma app_nil : forall m l,
    m = m ** l -> l = nil.
Proof.
  intros m. induction m; intros l H.
  + rewrite E0_left in H. congruence.
  + inversion H. now apply IHm.
Qed.

Lemma trace_prefix_asym : forall m1 m2,
    trace_prefix m1 m2 -> trace_prefix m2 m1 -> m1 = m2.
Proof.
  intros m1 m2 [l1 Hl1] [l2 Hl2]. rewrite Hl1 in Hl2.
  rewrite Eapp_assoc in Hl2. apply (app_nil m1 (l1 ** l2)) in Hl2.
  destruct l1, l2; try (rewrite E0_right in Hl1; congruence);
  try rewrite E0_right in Hl2; inversion Hl2.
Qed.
  
Lemma u_prefix_b_asym : forall P t1 t2,
    u_prefix_b P t1 t2 -> u_prefix_b P t2 t1 -> t1 = t2.
Proof.
  intros P t1 t2 [b1 [H11 [m1 [Hm1 Hm1']]]]  [b2 [H22 [m2 [Hm2 Hm2']]]].
  assert (behavior_prefix m1 t2) by now apply (behavior_prefix_pseudo_trans b1 m1 t2).
  assert (behavior_prefix m2 t1) by now apply (behavior_prefix_pseudo_trans b2 m2 t1).
  assert (trace_prefix m1 (snoc m2 (undef P))).
  { destruct H as [beh Hbeh]. rewrite Hm2' in Hbeh. destruct beh; inversion Hbeh.
    now exists t. }
  assert (trace_prefix m2 (snoc m1 (undef P))).
  { destruct H0 as [beh Hbeh]. rewrite Hm1' in Hbeh. destruct beh; inversion Hbeh.
    now exists t. }
  apply snoc_pref in H1. apply snoc_pref in H2.
  destruct H1, H2.
  + subst. repeat (rewrite no_nested). reflexivity.
  + rewrite H1 in Hm1'. rewrite no_nested in Hm1'. now subst.
  + rewrite H2 in Hm2'. rewrite no_nested in Hm2'. now subst.
  + apply (trace_prefix_asym m1 m2 H1) in H2. rewrite H2 in *.
    now rewrite Hm2'.
Qed.

Lemma u_prefix_b_trans : forall P t1 t2 t3,
    u_prefix_b P t1 t2 -> u_prefix_b P t2 t3 -> u_prefix_b P t1 t3.
Proof.
  intros P t1 t2 t3 [b1 [H11 [m1 [Hm1 Hm1']]]]  [b2 [H22 [m2 [Hm2 Hm2']]]].
  assert (trace_prefix m1 m2 \/ trace_prefix m2 m1).
  { assert (behavior_prefix m1 t2) by now apply (behavior_prefix_pseudo_trans b1 m1 t2).
    assert (behavior_prefix m2 t2).
    { exists (Goes_wrong (cons (undef P) nil)). simpl. now rewrite <- snoc_app. }
    now apply (same_extension m1 m2 t2). }
  destruct H.    
  + exists b2. split; try now auto.
    exists m1. split; try now auto.
    now apply (trace_prefix_trans m1 m2 b2).
  + assert (u_prefix_b P t2 t1).
    { exists m1. split.
      exists (Goes_wrong (cons (undef P) nil)). simpl.
      now rewrite <- snoc_app. now exists m2. }
    assert (t1 = t2).
    { apply (u_prefix_b_asym P t1 t2); try now auto.
      exists b1; split; try now auto. now exists m1. }
    rewrite H1 in *. exists b2. split; try now auto.
    now exists m2.
Qed.
                                       
    
(* z_minus is in Z_p *)
Lemma growth_lemma : forall (P : prg) (π : prop) (S : Safety π),
                     Z_class P (z_minus P π).
Proof.
  intros P π S. unfold Z_class. intros t H.
  unfold z_minus in *. rewrite de_morgan2 in H.
  destruct H as [H1 H2].
  rewrite not_ex_forall_not in H2. destruct (S t H1) as [m [Hm1 Hm2]].
  exists m. split; try now auto.
  intros t' [Hpref | Hundef]; rewrite de_morgan2.
  + split.
    ++ now apply Hm2.
    ++ intros [t0 [Hf1 Hf2]]. specialize (H2 t0). rewrite de_morgan1 in H2.
       destruct H2; try now auto.
       destruct Hf2 as  [b [Hb [m0 [Hm0 Hm00]]]]. 
       apply (behavior_prefix_pseudo_trans b m0 t' Hb) in Hm0.
       assert (trace_prefix m0 m \/ trace_prefix m m0) by
           now apply (same_extension m0 m t').
       destruct H0.
       +++ apply H. exists m0. split; try now auto.
           now apply (behavior_prefix_pseudo_trans m m0 t).
           exists m0. split; try now auto. now apply trace_prefix_ref.
       +++ apply (Hm2 t0); try now auto.
           apply (behavior_prefix_pseudo_trans m0 m t0); try now auto.
           exists (Goes_wrong (cons (undef P) nil)). simpl. now rewrite <- snoc_app.
  + split.
    ++ specialize (H2 t'). rewrite de_morgan1 in H2. destruct H2 as [K | K]; try now auto.
       exfalso. apply K. now exists m.
    ++ intros [t0 [H0 H00]]. specialize (H2 t0). rewrite de_morgan1 in H2.
       destruct H2; try now auto. 
       assert (u_prefix_b P t' t) by now exists m.
       apply H. now apply (u_prefix_b_trans P t0 t' t).
Qed. 

(* and is the smallest property in Z_p including π *)
Lemma minimality_lemma : forall (P : prg) (π phi : prop) (S: Safety π) (Z: Z_class P phi),
                                (forall b, π b -> phi b) ->
                                (forall b', z_minus P π b' -> phi b').
Proof. intros P pi phi S Z H b' zb'.
       unfold z_minus in zb'. rewrite Z_p_equivalent in Z. destruct Z as [Sphi ref_phi].
       destruct zb' as [k0 | [t [k1 k2]]].
       + apply (H b' k0).
       + destruct k2 as [m [Hm Hmm]]. unfold ref_cl in ref_phi. apply (H t) in k1.
         apply (ref_phi t k1 b'). now exists m.
Qed.
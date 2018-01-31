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

Variable prg prg' ctx ctx' event : Set.

CoInductive trace : Set :=
| tnil : trace
| tundef : prg -> trace
| tcons : event -> trace -> trace.


(* we can distinguish finite and infinite traces *)
Inductive fin : trace -> Prop :=
  | fnil : fin tnil
  | fundef : forall P, fin (tundef P)
  | fcons : forall e t, fin t -> fin (tcons e t).

Definition inf : trace -> Prop :=
  fun t : trace => ~ fin t.

Lemma fin_or_inf : forall t : trace,  fin t \/ inf t.
Proof. intros t; apply classic. Qed.

(* finite prefix relation over traces *)
Inductive prefix : trace -> trace -> Prop :=
  | pnil : forall t, prefix tnil t
  | pundef : forall P, prefix (tundef P) (tundef P)
  | pcons : forall e t1 t2, prefix t1 t2 -> prefix (tcons e t1) (tcons e t2).

Lemma pref_impl_fin : forall t t', prefix t t' -> fin t.
Proof. intros t t' Hprefix. induction Hprefix; now constructor. Qed.

Lemma inf_no_pref : forall t : trace,
    inf t -> (forall t' : trace, ~ prefix t t').
Proof. intros t Hinf t' Hprefix. apply Hinf. eapply pref_impl_fin. eassumption. Qed.

(* reflexivity for finite traces *)
Lemma prefix_refl : forall t : trace, fin t -> prefix t t.
Proof. intros t Hfin. induction Hfin; now constructor. Qed.

(* antisymmetry *)
Lemma prefix_antisymm : forall t t' : trace,
    prefix t t' -> prefix t' t -> t = t'.
Proof.
  intros t t' Hp1 Hp2. induction Hp1.
  - now inversion Hp2.
  - reflexivity.
  - f_equal. apply IHHp1. now inversion Hp2.
Qed.

(* transitivity *)
Lemma prefix_trans_aux : forall t1 t2 t3 : trace,
    fin t2 -> prefix t1 t2 -> prefix t2 t3 -> prefix t1 t3.
Proof.
  intros t1 t2 t3 Hfin2. generalize dependent t3. generalize dependent t1.
  induction Hfin2; intros t1 t3 Hp1 Hp2.
  - inversion Hp1. subst. now constructor.
  - inversion Hp2; now subst.
  - inversion Hp1. constructor. inversion Hp2. subst.
    constructor. now apply IHHfin2.
Qed.

(* the hp fin t2 is not really needed *)
Lemma prefix_trans : forall t1 t2 t3 : trace,
    prefix t1 t2 -> prefix t2 t3 -> prefix t1 t3.
Proof.
  intros t1 t2 t3 Hp12 Hp23. eapply (prefix_trans_aux _ t2).
  eapply pref_impl_fin. eassumption. assumption. assumption.
Qed.

(* prefixes of the same trace are comparable *)
Lemma prefix_comp : forall t m1 m2 : trace,
    prefix m1 t -> prefix m2 t -> (prefix m1 m2 \/ prefix m2 m1).
Proof.
  intros t m1 m2 Hp1 Hp2. pose proof (pref_impl_fin _ _ Hp1) as Hfin1.
  generalize dependent Hp2. generalize dependent Hp1.
  generalize dependent m2. generalize dependent t.
  induction Hfin1 as [| |e m1'].
  - left. now constructor.
  - intros t m2 Hp1 Hp2. inversion Hp1; subst. inversion Hp2; subst.
    + right. now constructor.
    + left. now constructor.
  - intros t m2 Hp1 Hp2. inversion Hp1; subst. inversion Hp2; subst.
    + right. constructor.
    + specialize (IHHfin1 _ _ H2 H1). destruct IHHfin1.
      * left. now constructor.
      * right. now constructor.
Qed.

(* Finite traces with no undefined behavior *)
Inductive fin_no_undef : trace -> Prop :=
  | fnunil : fin_no_undef tnil
  | fnucons : forall e t, fin_no_undef t -> fin_no_undef (tcons e t).

(* Finite traces with no undefined behavior are indeed finite *)
Lemma fin_no_undef_fin : forall {t}, fin_no_undef t -> fin t.
Proof. intros t H. induction H; now constructor. Qed.

(* Undef *)
CoFixpoint Undef (P:prg) (t:trace) : trace :=
  match t with
  | tnil => tundef P
  | tundef Q => tundef P 
  | tcons x xs => tcons x (Undef P xs)
  end.


Lemma Undef_nil : forall P,
  Undef P tnil = tundef P.
Proof.
  intro P. replace (Undef P tnil) with (match (Undef P tnil) with
                                        | tnil => tnil
                                        | tundef Q => tundef Q
                                        | tcons e t => tcons e t end).
  - reflexivity.
  - destruct (Undef P tnil); reflexivity.
Qed.

Lemma Undef_undef : forall P Q,
  Undef P (tundef Q) = tundef P.
Proof.
  intros P Q. replace (Undef P (tundef Q)) with (match (Undef P (tundef Q)) with
                                                | tnil => tnil
                                                | tundef Q => tundef Q
                                                | tcons e t => tcons e t end).
  - reflexivity.
  - destruct (Undef P (tundef Q)); reflexivity.
Qed.

Lemma Undef_cons : forall P e t,
  Undef P (tcons e t) = tcons e (Undef P t).
Proof.
  intros P e t. replace (Undef P (tcons e t)) with (match (Undef P (tcons e t)) with
                                                   | tnil => tnil
                                                   | tundef Q => tundef Q
                                                   | tcons e t => tcons e t end).
  - reflexivity.
  - destruct (Undef P (tcons e t)); reflexivity.
Qed.

(*
   prefixes of m;undef can only be:
   + equal to m;undef
   + prefixes of m
 *)

Lemma u_lemma0 : forall (P : prg) (m m' : trace),
    prefix m' (Undef P m) -> (m' = Undef P m) \/ prefix m' m.
Proof.
  intros P m m' Hprefix. remember (Undef P m) as mU.
  generalize dependent P. generalize dependent m.
  induction Hprefix.
  - intros m P HeqmU. right. now constructor.
  - intros m Q HeqmU. left. reflexivity.
  - intros m P HeqmU.
    destruct m as [| | e' m'].
    + rewrite Undef_nil in HeqmU. now inversion HeqmU.
    + rewrite Undef_undef in HeqmU. now inversion HeqmU.
    + rewrite Undef_cons in HeqmU. inversion HeqmU; subst.
      destruct (IHHprefix m' P eq_refl) as [IH | IH].
      * left. now f_equal.
      * right. now constructor.
Qed.

(* finite trace folowed by undef are still finite...  *)
Lemma u_fin : forall (P : prg) (m : trace), fin m -> fin (Undef P m).
Proof.
  intros P m H.
  - induction H.
    + rewrite Undef_nil. now do 2 constructor.
    + rewrite Undef_undef. now constructor.
    + rewrite Undef_cons. now constructor.
Qed.

(* and longer *)
Lemma u_fin_no_undef_prefix : forall (P : prg) (m : trace),
  fin_no_undef m -> prefix m (Undef P m).
Proof.
  intros P m H.
  - induction H.
    + rewrite Undef_nil. now do 2 constructor.
    + rewrite Undef_cons. now constructor.
Qed.

Lemma Undef_not_nil : forall P t, ~(tnil = Undef P t).
Proof.
  intros P t Hc.
  destruct t. + rewrite Undef_nil in Hc. now inversion Hc.
              + rewrite Undef_undef in Hc. now inversion Hc.
              + rewrite Undef_cons in Hc. now inversion Hc.
Qed.

Lemma Undef_tundef : forall P Q t,
  fin_no_undef t -> tundef P = Undef Q t -> t = tnil /\ P = Q.
Proof.
  intros P Q t Hfin H.
  destruct Hfin. + rewrite Undef_nil in H. now inversion H.
                 + rewrite Undef_cons in H. now inversion H.
Qed.

Lemma Undef_tcons : forall e t P t',
  tcons e t = Undef P t' -> exists t'', t' = tcons e t'' /\ t = Undef P t''.
Proof.
  intros e t P t' H.
  destruct t'. + rewrite Undef_nil in H. now inversion H.
               + rewrite Undef_undef in H. now inversion H.
               + rewrite Undef_cons in H. inversion H. subst. now eauto.
Qed.

(*
   traces ending with an undefined
   behavior have no continuations
 *)
Lemma u_end' : forall (P : prg) (m t: trace),
    prefix (Undef P m) t -> (Undef P m) = t.
Proof.
  intros P m t H. remember (Undef P m) as m'.
  generalize dependent m.
  induction H; intros m Heqm'.
  - now (apply Undef_not_nil in Heqm').
  - reflexivity.
  - f_equal.
    apply Undef_tcons in Heqm'.
    destruct Heqm' as [t'' [H1 H2]]. subst. eapply IHprefix. reflexivity.
Qed.

(* CH: Previous version just an awkward way to phrase the same thing *)
Lemma u_end : forall (P : prg) (t t': trace),
    (exists m : trace,  (Undef P m) = t) -> prefix t t' -> t = t'.
Proof. intros P t t' [m H] H0. subst t. now apply u_end'. Qed.

(*
  not used
*) 
Lemma no_nested_u : forall (P Q : prg) (m1 m2: trace),
  fin_no_undef m1 -> fin_no_undef m2 ->
  prefix (Undef P m1) (Undef Q m2) -> m1 = m2 /\ P = Q.
Proof.
  intros P Q m1 m2 Hf1 Hf2 Hp.
  remember (Undef P m1) as m1'. remember (Undef Q m2) as m2'.
  generalize dependent m2. generalize dependent m1.
  generalize dependent Q. generalize dependent P.
  induction Hp.
  - intros P Q m1 Hf1 Heqm1' m2 Hf2 Heqm2'. subst.
    now apply Undef_not_nil in Heqm1'.
  - intros P0 Q m1 Hf1 Heqm1' m2 Hf2 Heqm2'.
    apply (Undef_tundef _ _ _ Hf1) in Heqm1'. destruct Heqm1' as [H1 H1'].
    apply (Undef_tundef _ _ _ Hf2) in Heqm2'. destruct Heqm2' as [H2 H2'].
    now subst.
  - intros P Q m1 Hf1 Heqm1' m2 Hf2 Heqm2'. subst.
    apply Undef_tcons in Heqm1'. destruct Heqm1' as [m1' [H1 H1']].
    apply Undef_tcons in Heqm2'. destruct Heqm2' as [m2' [H2 H2']]. subst.
    assert (m1' = m2' /\ P = Q).
      eapply IHHp. now inversion Hf1. reflexivity.
                   now inversion Hf2. reflexivity.
    split. now f_equal. easy.
Qed.

Definition u_prefix (P : prg) (t1 t2: trace) : Prop :=
   exists m:trace, fin_no_undef m /\ prefix m t2 /\ (Undef P m = t1).

Lemma u_imp_fin : forall (P : prg) (t m: trace),
    u_prefix P t m -> fin t.
Proof. intros P t m u. rewrite dne. intros it.
       destruct u as [mt [fmt [pmtt H]]]. assert(ft : fin t).
       { rewrite <- H. apply (u_fin P mt (fin_no_undef_fin fmt)). }
       apply (it ft).
Qed.

Lemma Undef_fin_no_undef : forall P t, fin_no_undef (Undef P t) -> False.
Proof.
  intros P t H. remember (Undef P t) as t'.
  generalize dependent t. generalize dependent P.
  induction H.
  - intros P t Heqt'. now apply Undef_not_nil in Heqt'.
  - intros P t0 Heqt'. apply Undef_tcons in Heqt'. destruct Heqt' as [t'' [H1 H2]]. subst.
    now specialize (IHfin_no_undef _ _ eq_refl).
Qed.

Lemma u_trans : forall (P : prg) (m1 m2 t : trace),
    u_prefix P m1 m2 -> u_prefix P m2 t -> u_prefix P m1 t.
Proof.
  unfold u_prefix.
  intros P m1 m2 t [mt1 [f1 [p2 u1]]] [mt2 [f2 [pt u2]]].
  assert (K : mt1 = Undef P mt2 \/ prefix mt1 mt2).
  { apply (u_lemma0 P mt2 mt1). rewrite u2. assumption. }
  destruct K.
  + subst. now apply Undef_fin_no_undef in f1.
  + exists mt1. split. assumption. split. apply (prefix_trans mt1 mt2 t H pt).
    assumption.
Qed.

(* properties *)
Definition prop := trace -> Prop.

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

Lemma neg_rsat : forall (P : prg) (pi : prop),
       ~ rsat P pi <->
       (exists (C : ctx) (t: trace),
           sem (plug P C) t /\ ~ pi t).
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

Lemma neg_rsat' : forall (P : prg) (pi : prop),
       ~ rsat' (compile P) pi <->
       (exists (C' : ctx') (t: trace),
           sem' (plug' (compile P) C') t /\ ~ pi t).
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
     ((exists (C': ctx') (t' : trace),
       sem' (plug' (compile P) C') t' /\ ~ pi t') ->
      (exists (C : ctx) (t: trace),
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

Definition RSC_dc (P : prg) : Prop :=
  forall (C' : ctx') (t : trace), sem' (plug' (compile P) C') t ->
   (forall m : trace, fin m -> prefix m t ->  
      exists (C : ctx) (t' : trace), sem (plug P C) t' /\
            (prefix m t' \/ u_prefix P t' m)).

(*
   this formulation of Z_p is different from the one in the paper
   but we will prove equivalence later on
 *)
Definition Z_class (P: prg) (pi : prop) : Prop :=
  forall t : trace, ~ pi t ->
   (exists m : trace, fin m /\ prefix m t /\
          forall t' : trace, (prefix m t' \/ u_prefix P t' m) -> ~ pi t').

Theorem RSC_dc_RZP : forall P : prg,
    RSC_dc P -> (forall pi : prop, Z_class P pi -> RP P pi).
Proof.
  intros P r pi z. rewrite contra_RP. intros [C' [t [h0 h1]]].
  destruct (z t h1) as [m [fm [pmt H]]]. clear z.
  destruct (r C' t h0 m fm pmt) as [C [ t' [k0 k1]]]. clear r.
  exists C, t'. split. - assumption. - apply (H t' k1).
Qed.

Theorem RZP_RSC_dc : forall P : prg,
    (forall pi : prop, Z_class P pi -> RP P pi) -> RSC_dc P.
Proof.
  unfold RSC_dc. intros P rz C' t H0 m fm pmt.
  assert (K : Z_class P (fun b => ~ (prefix m b \/ u_prefix P b m))).
  { unfold Z_class. intros b hb. rewrite <- dne in hb.
    destruct hb as [pmb | ub].
    + exists m. split. assumption. split. assumption.
      intros b' [b1 | b2]; rewrite <- dne. left. assumption.
      right. assumption.
    + assert (fb : fin b). { apply (u_imp_fin P b m ub). }
      unfold u_prefix in ub. destruct ub as [mb [ fmt [mtb ub ]]].
      exists b. split. assumption. split. apply (prefix_refl b fb).
      intros b' [k1 | k2]. apply (u_end P b b') in k1. rewrite <- dne.
      right. rewrite <-  k1. unfold u_prefix. exists mb. apply (conj fmt (conj mtb ub)).
      exists mb. assumption. rewrite <- dne. right.
      unfold u_prefix in k2. destruct k2 as [m2 [f2 [ p2 u2]]].
      unfold u_prefix. rewrite <- ub in p2. apply (u_lemma0 P mb m2) in p2.
      destruct p2.
      rewrite H in u2. exfalso. symmetry in H. subst. now apply Undef_fin_no_undef in f2.
      apply (prefix_trans m2 mb m H) in mtb.
      exists m2. split. assumption. split; assumption.
  }
  assert (T : ~ (fun b => ~ (prefix m b \/ u_prefix P b m)) t).
  { rewrite <- dne. left. assumption. }
  specialize (rz (fun b => ~ (prefix m b \/ u_prefix P b m)) K).
  rewrite contra_RP in rz. destruct rz as [C [t' [k0 k1]]]. exists C',t. split. assumption.
  rewrite <- dne. left. assumption. exists C,t'.
  split. assumption. rewrite <- dne in k1. assumption.
Qed.

Corollary pointwise_equiv : forall P : prg,
    RSC_dc P <-> (forall pi : prop, Z_class P pi -> RP P pi).
Proof.
  intros P. split.
  - apply RSC_dc_RZP.
  - apply RZP_RSC_dc.
Qed.

Corollary more_standard :
    (forall P, RSC_dc P) <-> (forall P pi, Z_class P pi -> RP P pi).
   (* ^^^^^^^^^^^^^^^^ *)    (* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ *)
   (* standard RSC^DC  *)    (*      almost standard RP          *)
Proof.
  split. - intros H P. now apply RSC_dc_RZP.
         - intros H P. apply RZP_RSC_dc. now apply H.
Qed.

(*********************************************************)
(*  Relation between Z_p and Safety                      *)
(*********************************************************)

Definition Safety (pi : prop) : Prop :=
  forall t, ~ pi t -> exists m,
      fin m /\ prefix m t /\
        (forall t', prefix m t' -> ~ pi t').

(* Z_class is a sublclass of safety *)
Lemma Z_p_Safety : forall (P : prg) (pi : prop),
    Z_class P pi -> Safety pi.
Proof.
  unfold Safety. intros P pi Z t nt.
  destruct (Z t nt) as [m [fm [pmt H]]]. clear Z.
  exists m. split.
  - assumption.
  - split. assumption. intros t' h0. apply (H t' (or_introl (u_prefix P t' m) h0)).
Qed.


Definition ref_cl (P : prg) (pi : prop) : Prop :=
  forall t, pi t -> forall t', u_prefix P t t' -> pi t'.

(* classically equivalent formulation for ref_cl *)
Lemma ref_cl' : forall (P : prg) (pi : prop),
    ref_cl P pi <->
    forall t', ~ pi t' -> forall t, u_prefix P t t' -> ~ pi t.
Proof.
  intros P pi. split.
  - intros r t' nt' t utt' pit. apply (nt' (r t pit t' utt')).
  - unfold ref_cl. intros r t pit t' utt'. rewrite dne.
    intros npi'. apply ((r t' npi' t utt') pit).
Qed.

Lemma U_general : forall (P : prg) (t1 t2 : trace),
    u_prefix P t1 t2 ->
    (forall m, prefix m t2 ->
               (prefix m t1 \/ u_prefix P t1 m)).
Proof.
  intros P t1 t2 u12 m pm2. unfold u_prefix in u12.
  destruct u12 as [mm [fmm [pmm2 u1]]].
  assert (foo : prefix m mm \/ prefix mm m).
  { eapply (prefix_comp t2); assumption. }
  destruct foo as [k0 | k1].    
  + left. assert (foo : prefix mm t1). 
    { rewrite <- u1.
      apply u_fin_no_undef_prefix. assumption. }
    apply (prefix_trans m mm t1 k0 foo).
  + right. unfold u_prefix.
    exists mm. split. assumption.
    split; assumption.
Qed. 

Lemma Z_p_equivalent : forall (P : prg) (pi : prop),
    Z_class P pi <-> Safety pi /\ ref_cl P pi.
Proof.
  intros P pi. split.
  - intros z. split.
    + eapply Z_p_Safety. apply z.
    + rewrite ref_cl'. intros t' nt' t utt'.
      destruct (z t' nt') as [m [fm [pmt zz]]].
      assert (prefix m t \/ u_prefix P t m) as use_me by
      apply (U_general P t t' utt' m pmt).
      apply (zz t use_me).      
  -  intros [s r]. unfold Z_class.
     intros t nt. destruct (s t nt) as [m [fm [pmt H]]].
     exists m. split. assumption.
     split. assumption. intros t' [k0 | k1].
     apply (H t' k0). assert (use_me : u_prefix P t' t).
     { unfold u_prefix. destruct k1 as [m0 [f0 [p0 u0]]].
       exists m0. split. assumption. split.
       apply (prefix_trans m0 m t p0 pmt).
       assumption. }       
     rewrite ref_cl' in r. apply (r t nt t' use_me).
Qed.

Lemma easy_lemma0 :
  (forall P pi, Z_class P pi -> RP P pi) <->
  (forall P pi, (Safety pi /\ ref_cl P pi) -> RP P pi).
Proof.
  split.
  - intros L P pi H. rewrite <- (Z_p_equivalent P pi) in H.
    apply (L P pi H).
  - intros R P pi Z. rewrite (Z_p_equivalent P pi) in Z.
    apply (R P pi Z).
Qed.

Lemma easy_lemma1 : forall P : prg,
  (forall  pi, Z_class P pi -> RP P pi) <->
  (forall  pi, (Safety pi /\ ref_cl P pi) -> RP P pi).
Proof.
  intros P. split.
  - intros L pi H. rewrite <- (Z_p_equivalent P pi) in H.
    apply (L pi H).
  - intros R pi H. rewrite (Z_p_equivalent P pi) in H.    
    apply (R pi H).
Qed.

(* theorem in the paper *)
Corollary RSC_dc_equiv2 : 
  (forall P : prg, RSC_dc P) <->
  (forall P pi, (Safety pi /\ ref_cl P pi) -> RP P pi).
Proof. rewrite <- easy_lemma0. apply more_standard. Qed.

Corollary pointwise_equiv2 : forall P : prg,
    RSC_dc P <->
    (forall pi : prop, (Safety pi /\ ref_cl P pi) -> RP P pi).
Proof.
  intros P.
  rewrite <- (easy_lemma1 P). apply pointwise_equiv.
Qed.


(*********************************************************)
(*  extracting a Z_class property from a Safety one      *)
(*********************************************************)

Definition pi_z (pi : prop) (S:Safety pi) (P : prg) : prop :=
  fun t : trace =>
    pi t /\ forall (t' : trace), u_prefix P t t' -> pi t'.

Lemma sub : forall (pi : prop) (S : Safety pi)
                   (P : prg) (b : trace),
                    (pi_z pi S P b) -> pi b.
Proof. intros pi S P b [h0 h1]; assumption. Qed.

Lemma sub' : forall (pi : prop) (S : Safety pi)
                    (P : prg) (b : trace),
                     ~ pi b -> ~ (pi_z pi S P b).
Proof. intros pi S P b. rewrite <- contra.  
       apply (sub pi S P).
Qed.

(* the property pi_z is indeed in Z_p *)
Lemma extraction_lemma :  forall (pi : prop) (P : prg)
                                 (s : Safety pi),
                           Z_class P (pi_z pi s P).
Proof.
  intros pi P s. rewrite Z_p_equivalent. split.
  - unfold Safety. intros t nt.
    unfold pi_z in nt. rewrite de_morgan1 in nt.
    destruct nt as [k0 | k1].
    + destruct (s t k0) as [m [a1 [a2 a3]]].
      exists m. split. assumption. split. assumption.
      intros t' H. specialize (a3 t' H).
      apply (sub' pi s P t' a3).
    + rewrite not_forall_ex_not in k1.
      destruct k1 as [m k]. rewrite not_imp in k.
      destruct k as [k00 k11]. exists t.
      assert (ft : fin t) by apply (u_imp_fin P t m k00).
      split. assumption.
      split. apply (prefix_refl t ft).
      intros t' ptt'. apply (u_end P) in ptt'.
      rewrite <- ptt'. unfold pi_z. rewrite de_morgan1.
      right. rewrite not_forall_ex_not. exists m. rewrite not_imp.
      split;assumption. unfold u_prefix in k00.
      destruct k00 as [m0 [foo0 [ foo1 use_me]]].
      exists m0; assumption.
  - rewrite ref_cl'. intros t nt t' utt'.
    unfold pi_z in nt. rewrite de_morgan1 in nt.
    unfold pi_z. rewrite de_morgan1.
    destruct nt as [k0 | k1].
    right. intros H. apply (k0 (H t utt')).
    rewrite not_forall_ex_not in k1. destruct k1 as [m k].
    rewrite not_imp in k. destruct k as [k1 k2].
    right. rewrite not_forall_ex_not. exists m. rewrite not_imp.
    split. apply (u_trans P t' t m); assumption. assumption.
Qed.

(* pi_z is the biggest property in Z_p that is included in pi *)
Lemma maximality_lemma : forall (P : prg) (pi phi : prop) (S : Safety pi)
                                (Zphi : Z_class P phi)
                                (H: forall b, phi b -> pi b),

    forall b, phi b -> (pi_z pi S P) b.
Proof.
  intros P pi phi S Zphi H b phib.
  unfold pi_z. split.
  - apply (H b phib).
  - intros t ubt. rewrite dne. intros npit.
    assert (nphit : ~ phi t).
    { intros phit. apply (npit (H t phit)). }
    specialize (Zphi t nphit).
    destruct Zphi as [m [fm [pmt K]]].
    assert (use_me : prefix m b \/ u_prefix P b m).
    { apply (U_general P b t ubt m pmt). }
    apply ((K b use_me) phib).
Qed.


(*********************************************************)
(*  building a Z_class property on a Safety one          *)
(*********************************************************)

Definition z_minus (P : prg) (pi : prop) : prop :=
  fun b : trace =>
    pi b \/ (exists t, pi t /\ (u_prefix P t b \/ prefix b t)).

(* pi is included in z_minus *)
Lemma sub_minus : forall (P : prg) (pi : prop) (b : trace),
                  pi b -> (z_minus P pi) b.
Proof. intros P pi b H.  unfold z_minus. left. apply H. Qed.    

(* z_minus is in Z_p *)
Lemma growth_lemma : forall (P : prg) (pi : prop) (S : Safety pi),
                     Z_class P (z_minus P pi).
Proof.
  intros P pi S. rewrite Z_p_equivalent. split.
  - unfold Safety. intros b nb. unfold z_minus in nb.
    rewrite de_morgan2 in nb. destruct nb as [npib nn].
    destruct (S b npib) as [m [fm [pmb H]]].
    exists m. split. assumption. split. assumption.
    intros  b' pmb'. unfold z_minus. rewrite de_morgan2. split.
    + apply (H b' pmb').
    + intros [t [pit [k0 | k1]]].
      unfold u_prefix in k0. destruct k0 as [x [fx [pxb' uxt]]].
      assert (foo : prefix x m \/ prefix m x).
      { apply (prefix_comp b'); assumption. } destruct foo as [k | k].
      assert (use_me : u_prefix P t b).
      { unfold u_prefix. exists x. split. assumption.
        split. apply (prefix_trans x m b); assumption. assumption. }
      apply nn. exists t. split. assumption.
      left. assumption.
      assert (use_me : prefix x t).
      { rewrite  <- uxt. apply u_fin_no_undef_prefix. assumption. }
      apply (prefix_trans m x t k) in use_me. apply ((H t use_me) pit).
      apply (prefix_trans m b' t pmb') in k1. apply ((H t k1) pit).
  - unfold ref_cl. intros b [k0 | [t [pit K]]] b' H.
    + unfold z_minus. right. exists b. split. assumption. left. assumption.
    + destruct K. unfold z_minus. right. exists t. split. assumption. left.
      apply (u_trans P t b b'); assumption.
      unfold z_minus. right. assert (h : t = b).
      { destruct H as [m [fm [pmb' ub]]].
        rewrite <- ub in H0. rewrite <- ub. symmetry. apply (u_end' P); assumption. }
      exists t. split. assumption. left. rewrite h. assumption.
Qed.

(* and is the smallest property in Z_p including pi *)
Lemma minimality_lemma : forall (P : prg) (pi phi : prop) (S: Safety pi) (Z: Z_class P phi),
                                (forall b, pi b -> phi b) ->
                                (forall b', z_minus P pi b' -> phi b').
Proof. intros P pi phi S Z H b' zb'.
       unfold z_minus in zb'. rewrite Z_p_equivalent in Z. destruct Z as [Sphi ref_phi].
       destruct zb' as [k0 | [t [k1 k2]]].
       + apply (H b' k0).
       + destruct k2. unfold ref_cl in ref_phi. apply (H t) in k1.
         apply (ref_phi t k1 b' H0).
         unfold Safety in Sphi. rewrite dne. intros ff.
         destruct (Sphi b' ff) as [m [fm [pmb' K]]]. clear Sphi.
         apply (prefix_trans m b' t pmb') in H0. apply ((K t H0) (H t k1)).
Qed.
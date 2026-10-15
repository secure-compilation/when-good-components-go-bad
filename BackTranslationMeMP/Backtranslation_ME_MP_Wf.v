Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Traces.
Require Import CompCert.Events.
Require Import Common.CompCertExtensions.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.
Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.RSC_ME_MP_Faithful.
Require Import Backtranslation_ME_MP.
Require Import Backtranslation_ME_MP_Layout.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Lemma in_catl (T : Type) (x : T) (l1 l2 : seq T) : List.In x l1 -> List.In x (l1 ++ l2).
Proof. elim: l1 => [//|y l IH] /= [->|H]; [left | right; exact: IH]; by []. Qed.

Lemma in_catr (T : Type) (x : T) (l1 l2 : seq T) : List.In x l2 -> List.In x (l1 ++ l2).
Proof. elim: l1 => [//|y l IH] /= H. right. exact: IH. Qed.

Lemma in_cat_or (T : Type) (x : T) (l1 l2 : seq T) :
  List.In x (l1 ++ l2) -> List.In x l1 \/ List.In x l2.
Proof.
elim: l1 => [|y l IH] /= H; first by right.
case: H => [->|H]; first by left; left.
case: (IH H) => H'; [left; right | right]; by [].
Qed.

Lemma in_flat_map (A B : Type) (f : A -> seq B) (l : seq A) x :
  List.In x (flatten (map f l)) -> exists a, List.In a l /\ List.In x (f a).
Proof.
elim: l => [//|a l IH] /= Hx.
case: (List.in_app_or _ _ _ Hx) => H; first by exists a; split; [left|].
have [a' [H1 H2]] := IH H. exists a'. split; [right|]; by [].
Qed.

Lemma in_flat_map_intro (A B : Type) (f : A -> seq B) (l : seq A) a x :
  List.In a l -> List.In x (f a) -> List.In x (flatten (map f l)).
Proof.
elim: l => [//|b l IH] /= [<-|Ha] Hx; apply: List.in_or_app; first by left.
right. exact: IH Ha Hx.
Qed.

Lemma in_mem_seq (T : eqType) (x : T) (l : seq T) : List.In x l -> x \in l.
Proof. elim: l => [//|y l IH] /= [->|H]; rewrite inE; first by rewrite eqxx. by rewrite IH ?orbT. Qed.

Lemma mem_in_seq (T : eqType) (x : T) (l : seq T) : x \in l -> List.In x l.
Proof.
elim: l => [//|y l IH]. rewrite inE => /orP [/eqP ->|H]; first by left.
right. exact: IH.
Qed.

Lemma In_tagged cid (l : seq minstr) x :
  List.In x (rp_tagged cid l) -> x.2 = def_mem_tag cid true /\ List.In x.1 l.
Proof. rewrite /rp_tagged => /List.in_map_iff [i [<- Hi]]. by split. Qed.

Definition bnzs (l : seq minstr) : seq nat :=
  pmap (fun i => if i is MrBnz _ x then Some x else None) l.

Definition jals (l : seq minstr) : seq nat :=
  pmap (fun i => if i is MrJal x then Some x else None) l.

Lemma bnzs_cat l1 l2 : bnzs (l1 ++ l2) = bnzs l1 ++ bnzs l2.
Proof. by rewrite /bnzs pmap_cat. Qed.

Lemma jals_cat l1 l2 : jals (l1 ++ l2) = jals l1 ++ jals l2.
Proof. by rewrite /jals pmap_cat. Qed.

Lemma bnzs_flatten (ls : seq (seq minstr)) : bnzs (flatten ls) = flatten (map bnzs ls).
Proof. elim: ls => [//|l ls IH] /=. by rewrite bnzs_cat IH. Qed.

Lemma jals_flatten (ls : seq (seq minstr)) : jals (flatten ls) = flatten (map jals ls).
Proof. elim: ls => [//|l ls IH] /=. by rewrite jals_cat IH. Qed.

Lemma bnzs_load N r tmp : bnzs (rp_load N r tmp) = [::].
Proof. rewrite /rp_load. by case: ifP. Qed.

Lemma jals_load N r tmp : jals (rp_load N r tmp) = [::].
Proof. rewrite /rp_load. by case: ifP. Qed.

Lemma bnzs_init L t cid A j : bnzs (rp_init L t cid A j) = [:: rp_lab L cid j].
Proof. by rewrite /rp_init !bnzs_cat bnzs_load. Qed.

Lemma jals_init L t cid A j : jals (rp_init L t cid A j) = [:: alloc_label].
Proof. by rewrite /rp_init !jals_cat jals_load. Qed.

Lemma bnzs_test L cid k : bnzs (rp_test L cid k) = [:: rp_lab L cid (4 + k)].
Proof. by rewrite /rp_test bnzs_cat bnzs_load. Qed.

Lemma jals_test L cid k : jals (rp_test L cid k) = [::].
Proof. by rewrite /rp_test jals_cat jals_load. Qed.

Lemma bnzs_disp L cid A n :
  bnzs (rp_disp L cid A n) = [seq rp_lab L cid (4 + k) | k <- iota 0 n].
Proof.
rewrite /rp_disp !bnzs_cat bnzs_flatten -map_comp.
rewrite (eq_map (fun k => bnzs_test L cid k)) cats0 /=.
by elim: (iota 0 n) => [|k ks IH] //=; rewrite IH.
Qed.

Lemma jals_disp L cid A n : jals (rp_disp L cid A n) = [::].
Proof.
rewrite /rp_disp !jals_cat jals_flatten -map_comp.
rewrite (eq_map (fun k => jals_test L cid k)) /=.
by elim: (iota 0 n) => [|k ks IH] //=.
Qed.

Lemma bnzs_case L P C cid ke : bnzs (rp_case L P C cid ke) = [::].
Proof.
rewrite /rp_case bnzs_cat /rp_case_body.
case: ke.2 => [? ? z ?|? z ?]; by rewrite !bnzs_cat bnzs_load.
Qed.

Lemma jals_case L P C cid ke :
  jals (rp_case L P C cid ke)
  = if ke.2 is ECall _ P' _ C' then [:: mk_entry L P C C' P'; rp_lab L cid 0] else [::].
Proof.
rewrite /rp_case jals_cat /rp_case_body.
case: ke.2 => [? ? z ?|? z ?]; by rewrite !jals_cat jals_load.
Qed.

Lemma in_pmap (A : Type) (B : eqType) (f : A -> option B) (s : seq A) y :
  y \in pmap f s -> exists x, List.In x s /\ f x = Some y.
Proof.
elim: s => [//|x s IH] /=. case E: (f x) => [v|] /=.
- rewrite inE => /orP [/eqP ->|H]; first by exists x; split; [left|].
  have [x' [H1 H2]] := IH H. exists x'. split; [right|]; by [].
- move=> H. have [x' [H1 H2]] := IH H. exists x'. split; [right|]; by [].
Qed.

Lemma in_pmap_intro (A : Type) (B : eqType) (f : A -> option B) (s : seq A) x y :
  List.In x s -> f x = Some y -> y \in pmap f s.
Proof.
elim: s => [//|x' s IH] /= [<-|H] Hf.
- by rewrite Hf inE eqxx.
- case: (f x') => [v|] /=; last exact: IH H Hf.
  by rewrite inE (IH H Hf) orbT.
Qed.

Lemma clabs_In (cd : @Merged.code mt) l :
  l \in clabs cd -> exists tg, List.In (MrLabel l, tg) cd.
Proof.
rewrite /clabs /ilabs => H. have [i [Hi Hf]] := in_pmap H.
have [[i' tg] [Ei Hin]] := (List.in_map_iff _ _ _).1 Hi. rewrite /= in Ei. subst i'. clear Hi H.
case: i Hf Hin => // l' [<-] Hin. by exists tg.
Qed.

Lemma clabs_intro (cd : @Merged.code mt) l tg :
  List.In (MrLabel l, tg) cd -> l \in clabs cd.
Proof.
move=> H. rewrite /clabs /ilabs. apply: (in_pmap_intro (x := MrLabel l)); last by [].
exact: (List.in_map fst _ _ H).
Qed.

Lemma clabs_findopt (cd : @Merged.code mt) l :
  l \in clabs cd -> exists m, findopt (is_label_def l) cd = Some m.
Proof.
move=> /clabs_In [tg H]. apply: (findopt_In_ex H). by rewrite /is_label_def /= eqxx.
Qed.

Lemma uniq_label_pos (cd : @Merged.code mt) l n m t1 t2 :
  uniq (clabs cd) ->
  List.nth_error cd n = Some (MrLabel l, t1) -> List.nth_error cd m = Some (MrLabel l, t2) ->
  n = m.
Proof.
elim: cd n m => [|[i tg] cd IH] [|n] [|m] //=.
- move=> Hu [Ei _] Hm. subst i.
  have Hin := clabs_intro (List.nth_error_In _ _ Hm).
  move: Hu. by rewrite /clabs /= Hin.
- move=> Hu Hn [Ei _]. subst i.
  have Hin := clabs_intro (List.nth_error_In _ _ Hn).
  move: Hu. by rewrite /clabs /= Hin.
- move=> Hu Hn Hm. congr S. apply: IH Hn Hm.
  move: Hu. rewrite /clabs /=. case: i => //=. move=> l' /andP [_ H]. exact: H.
Qed.

Section Wf.

Variables (L P C : nat) (PI : Program.interface)
          (PB : NMap {fmap Block.id -> nat + seq value}) (t : trace).

Local Notation cc := (rp_comp_code L P C PI PB t).

Definition body (cid : nat) : seq minstr :=
  (if cid == Component.main then rp_init L t cid (rp_addr PB cid) 1 ++ rp_goto L cid 0 else [::])
  ++ flatten [seq MrMov (inl R_RA) (inl R_AUX2) :: rp_goto L cid 3 | p <- rp_exports PI cid]
  ++ Tl L P C PB t cid.

Lemma cc_in cid i tg :
  List.In (i, tg) (cc cid) ->
  (tg = def_mem_tag cid true /\ List.In i (body cid))
  \/ (exists p, [/\ List.In p (rp_exports PI cid), i = MrLabel (mk_entry L P C cid p)
                  & tg = Transitional.head_tag_gen PI cid p]).
Proof.
rewrite (cc_split L P C PI PB t) => H.
case: (in_cat_or H) => {}H.
- left. move: H. rewrite /Sc /body. case: (cid == Component.main) => H; last by case: H.
  have [E Hi] := In_tagged H. split; first exact: E.
  exact: in_catl Hi.
- case: (in_cat_or H) => {}H.
  + rewrite /Ec in H. have [p [Hp Hx]] := in_flat_map H.
    have Hx' : (MrLabel (mk_entry L P C cid p), Transitional.head_tag_gen PI cid p) = (i, tg)
               \/ List.In (i, tg) (rp_tagged cid (MrMov (inl R_RA) (inl R_AUX2) :: rp_goto L cid 3))
      := Hx.
    case: Hx' => [Ex|Hx2].
    * right. exists p. case: Ex => Ei Et. by split.
    * left. have [E Hi] := In_tagged Hx2. split; first exact: E.
      apply: in_catr. apply: in_catl.
      apply: (in_flat_map_intro Hp). exact: Hi.
  + left. have [E Hi] := In_tagged H. split; first exact: E.
    apply: in_catr. apply: in_catr. exact: Hi.
Qed.

Lemma lab_in_cc cid j :
  (j \in [:: 0; 2; 3]) || ((cid == Component.main) && (j == 1))
  || (4 <= j < 4 + size (rp_events t cid)) ->
  rp_lab L cid j \in clabs (cc cid).
Proof.
rewrite clabs_comp !mem_cat => /orP [/orP [Hj|/andP [/eqP Hm /eqP Ej]]|/andP [H1 H2]].
- apply/orP; right. apply/orP; right. apply/orP; left.
  move: Hj. rewrite !inE => /orP [/eqP ->|/orP [/eqP ->|/eqP ->]].
  + by rewrite eqxx !orbT.
  + by rewrite eqxx !orbT.
  + by rewrite eqxx.
- apply/orP; left. rewrite Hm Ej eqxx. by rewrite inE eqxx.
- apply/orP; right. apply/orP; right. apply/orP; right.
  apply/mapP. exists (j - 4); last by rewrite subnKC.
  rewrite mem_iota add0n. apply/andP; split; first by [].
  clear -H1 H2. lia.
Qed.

Lemma Tl_eq cid :
  Tl L P C PB t cid
  = MrLabel (rp_lab L cid 3)
    :: rp_init L t cid (rp_addr PB cid) 2 ++ rp_push ++ rp_goto L cid 0
       ++ rp_disp L cid (rp_addr PB cid) (size (rp_events t cid))
       ++ flatten [seq rp_case L P C cid ke
                    | ke <- zip (iota 0 (size (rp_events t cid))) (rp_events t cid)]
       ++ [:: MrHalt].
Proof. by []. Qed.

Lemma bnzs_body cid l : l \in bnzs (body cid) -> l \in clabs (cc cid).
Proof.
have Ee : forall p : nat, (bnzs \o (fun _ => MrMov (inl R_RA) (inl R_AUX2) :: rp_goto L cid 3)) p = [::]
  by [].
have Hfl : forall (T : Type) (s : seq T), flatten [seq ([::] : seq nat) | _ <- s] = [::]
  by move=> T; elim=> //.
have Ec : forall x (l0 : seq minstr), bnzs (MrLabel x :: l0) = bnzs l0 by [].
have Ep : bnzs rp_push = [::] by [].
have Eg : forall j, bnzs (rp_goto L cid j) = [::] by [].
have Eh : bnzs [:: @MrHalt mt] = [::] by [].
rewrite /body Tl_eq bnzs_cat mem_cat => /orP [Hm|Hm].
- move: Hm. case Em: (cid == Component.main); last by rewrite /= in_nil.
  rewrite bnzs_cat bnzs_init Eg mem_cat inE orbF => /eqP ->.
  apply: lab_in_cc. by rewrite Em eqxx orbT.
- move: Hm. rewrite bnzs_cat mem_cat => /orP [Hm|Hm].
  + move: Hm. by rewrite bnzs_flatten -map_comp (eq_map Ee) Hfl in_nil.
  + move: Hm. rewrite Ec bnzs_cat bnzs_init mem_cat inE => /orP [/eqP ->|Hm].
    * apply: lab_in_cc. by rewrite !inE eqxx orbT.
    * move: Hm. rewrite bnzs_cat Ep cat0s bnzs_cat Eg cat0s bnzs_cat bnzs_disp mem_cat.
      move=> /orP [Hm|Hm].
      -- move: Hm => /mapP [k Hk ->]. apply: lab_in_cc.
         move: Hk. rewrite mem_iota add0n => /andP [_ Hk].
         apply/orP; right. apply/andP; split; first by rewrite leq_addr.
         by rewrite ltn_add2l.
      -- move: Hm. rewrite bnzs_cat bnzs_flatten -map_comp.
         by rewrite (eq_map (fun ke => bnzs_case L P C cid ke)) Hfl Eh in_nil.
Qed.

Lemma jals_body cid l : l \in jals (body cid) ->
  [\/ l \in clabs (cc cid), l = alloc_label
    | exists P' z C', List.In (ECall cid P' z C') t /\ l = mk_entry L P C C' P'].
Proof.
have Ee : forall p : nat,
    (jals \o (fun _ => MrMov (inl R_RA) (inl R_AUX2) :: rp_goto L cid 3)) p = [:: rp_lab L cid 3]
  by [].
have Ec : forall x (l0 : seq minstr), jals (MrLabel x :: l0) = jals l0 by [].
have Ep : jals rp_push = [::] by [].
have Eg : forall j, jals (rp_goto L cid j) = [:: rp_lab L cid j] by [].
have Eh : jals [:: @MrHalt mt] = [::] by [].
have L0 : rp_lab L cid 0 \in clabs (cc cid) by apply: lab_in_cc; rewrite !inE eqxx.
have L3 : rp_lab L cid 3 \in clabs (cc cid) by apply: lab_in_cc; rewrite !inE eqxx !orbT.
rewrite /body Tl_eq jals_cat mem_cat => /orP [Hm|Hm].
- move: Hm. case Em: (cid == Component.main); last by rewrite /= in_nil.
  rewrite jals_cat jals_init Eg mem_cat !inE => /orP [/eqP ->|/eqP ->].
  + exact: Or32.
  + exact: Or31.
- move: Hm. rewrite jals_cat mem_cat => /orP [Hm|Hm].
  + move: Hm. rewrite jals_flatten -map_comp (eq_map Ee).
    case/flattenP => ls /mapP [p _ ->]. rewrite inE => /eqP ->. exact: Or31.
  + move: Hm. rewrite Ec jals_cat jals_init mem_cat inE => /orP [/eqP ->|Hm].
    * exact: Or32.
    * move: Hm. rewrite jals_cat Ep cat0s jals_cat Eg mem_cat inE => /orP [/eqP ->|Hm].
      -- exact: Or31.
      -- move: Hm. rewrite jals_cat jals_disp cat0s jals_cat jals_flatten -map_comp Eh cats0.
         case/flattenP => ls /mapP [ke Hke ->].
         rewrite -[(jals \o _) ke]/(jals (rp_case L P C cid ke)) jals_case.
         have Hke2 : ke.2 \in rp_events t cid.
         { have H := map_f snd Hke.
           rewrite -/(unzip2 _) unzip2_zip ?size_iota // in H. }
         move: Hke2. rewrite mem_filter.
         case: ke.2 => [X P' z C'|X z C'] /andP [HX Hin]; last by rewrite in_nil.
         rewrite !inE => /orP [/eqP ->|/eqP ->]; last exact: Or31.
         apply: Or33. exists P', z, C'. split; last by [].
         move: HX => /= /eqP <-. exact: mem_in_seq Hin.
Qed.

Lemma ilabs_body cid l : l \in ilabs (body cid) ->
  exists j, j < 4 + size (rp_events t cid) /\ l = rp_lab L cid j.
Proof.
have Ee : forall p : nat, (ilabs \o (fun _ => MrMov (inl R_RA) (inl R_AUX2) :: rp_goto L cid 3)) p = [::]
  by [].
have Hfl : forall (T : Type) (s : seq T), flatten [seq ([::] : seq nat) | _ <- s] = [::]
  by move=> T; elim=> //.
have Ec : forall x (l0 : seq minstr), ilabs (MrLabel x :: l0) = x :: ilabs l0 by [].
have Ep : ilabs rp_push = [::] by [].
have Eg : forall j, ilabs (rp_goto L cid j) = [::] by [].
have Eh : ilabs [:: @MrHalt mt] = [::] by [].
have Hj : forall j, j < 4 -> exists j', j' < 4 + size (rp_events t cid) /\ rp_lab L cid j = rp_lab L cid j'.
{ move=> j Hj. exists j. split=> //. exact: leq_trans Hj (leq_addr _ _). }
rewrite /body Tl_eq ilabs_cat mem_cat => /orP [Hm|Hm].
- move: Hm. case Em: (cid == Component.main); last by rewrite /= in_nil.
  rewrite ilabs_cat ilabs_init Eg mem_cat inE orbF => /eqP ->. exact: Hj.
- move: Hm. rewrite ilabs_cat mem_cat => /orP [Hm|Hm].
  + move: Hm. by rewrite ilabs_flatten -map_comp (eq_map Ee) Hfl in_nil.
  + move: Hm. rewrite Ec inE => /orP [/eqP ->|Hm]; first exact: Hj.
    move: Hm. rewrite ilabs_cat ilabs_init inE => /orP [/eqP ->|Hm]; first exact: Hj.
    move: Hm. rewrite ilabs_cat Ep cat0s ilabs_cat Eg cat0s ilabs_cat ilabs_disp inE.
    move=> /orP [/eqP ->|Hm]; first exact: Hj.
    move: Hm. rewrite ilabs_cat ilabs_flatten -map_comp Eh cats0.
    case/flattenP => ls /mapP [ke Hke ->].
    rewrite -[(ilabs \o _) ke]/(ilabs (rp_case L P C cid ke)) ilabs_case inE => /eqP ->.
    exists (4 + ke.1). split; last by [].
    have H := map_f fst Hke.
    rewrite -/(unzip1 _) unzip1_zip ?size_iota // mem_iota add0n in H.
    by rewrite ltn_add2l.
Qed.

Lemma in_map_In (A : Type) (B : eqType) (f : A -> B) (s : seq A) y :
  y \in map f s -> exists x, List.In x s /\ y = f x.
Proof.
elim: s => [//|x s IH] /=. rewrite inE => /orP [/eqP ->|H]; first by exists x; split; [left|].
have [x' [H1 H2]] := IH H. exists x'. split; [right|]; by [].
Qed.

Lemma in_map_intro (A : Type) (B : eqType) (f : A -> B) (s : seq A) x :
  List.In x s -> f x \in map f s.
Proof. elim: s => [//|y s IH] /= [->|H]; rewrite inE; first by rewrite eqxx. by rewrite IH ?orbT. Qed.

Lemma cc_color' cid i tg : List.In (i, tg) (cc cid) -> color tg = cid.
Proof. by case/cc_in => [[-> _]|[p [_ _ ->]]]. Qed.

Lemma Tl_in cid : List.In (MrLabel (rp_lab L cid 3), def_mem_tag cid true) (cc cid).
Proof.
rewrite (cc_split L P C PI PB t). apply: in_catr. apply: in_catr.
rewrite Tl_eq. by left.
Qed.

Section Prog.

Variables (I : Program.interface) (B : NMap {fmap Block.id -> nat + seq value}).

Local Notation q := (rp_program L P C PI PB t I B).

Hypothesis HI : forall c, c \in domm I -> PI c = I c.
Hypothesis Hok : forall c, c \in domm I -> comp_ok L P C PI t c.
Hypothesis Hcalls : forall C0 P0 z0 C', List.In (ECall C0 P0 z0 C') t ->
  [/\ P0 \in rp_exports PI C', C0 <> C'
    & C0 \in odflt [::] (omap snd (entry (Transitional.head_tag_gen PI C' P0)))].
Hypothesis Hsound : sound_interface I.
Hypothesis HIB : domm I = domm B.
Hypothesis Hreq : forall c, I c ->
  exists b, match Option.bind (fun r : {fmap Block.id -> nat + seq value} => r b) (B c) with
            | None => False
            | Some buf => match buf with inl n => n > 0 | inr vs => length vs > 0 end
            end.

Lemma Ecode : code q = flatten [seq cc c | c <- domm I].
Proof. by []. Qed.

Lemma q_in x : List.In x (code q) -> exists c, c \in domm I /\ List.In x (cc c).
Proof.
rewrite Ecode => H. have [c [Hc Hx]] := in_flat_map H.
exists c. split; [exact: in_mem_seq Hc | exact: Hx].
Qed.

Lemma q_intro c x : c \in domm I -> List.In x (cc c) -> List.In x (code q).
Proof. move=> Hc Hx. rewrite Ecode. exact: (in_flat_map_intro (mem_in_seq Hc) Hx). Qed.

Lemma q_uniq : uniq (clabs (code q)).
Proof.
rewrite Ecode clabs_flatten -map_comp. apply: flatten_clabs_uniq; first exact: uniq_fset.
exact: Hok.
Qed.

Lemma q_clabs c l : c \in domm I -> l \in clabs (cc c) -> l \in clabs (code q).
Proof.
move=> Hc /clabs_In [tg H]. exact: clabs_intro (q_intro Hc H).
Qed.

Lemma exp_rp c p : exported_procedure I c p -> c \in domm I /\ p \in rp_exports PI c.
Proof.
case=> CI [Hc He].
have Hd : c \in domm I by apply/dommP; exists CI.
split=> //. rewrite /rp_exports (HI Hd) Hc /=. exact: He.
Qed.

Lemma entry_cell c p : c \in domm I -> p \in rp_exports PI c ->
  List.In (MrLabel (mk_entry L P C c p), Transitional.head_tag_gen PI c p) (code q).
Proof.
move=> Hc Hp. apply: (q_intro Hc). rewrite (cc_split L P C PI PB t).
apply: in_catr. apply: in_catl. rewrite /Ec.
apply: (in_flat_map_intro (mem_in_seq Hp)). by left.
Qed.

Lemma rp_wf : well_formed_program q.
Proof.
split.
- exact: Hsound.
- apply/eq_fset => c. apply/idP/idP => Hc.
  + have H := q_intro Hc (Tl_in c). rewrite /get_procedures in_fset.
    exact: (in_map_intro (fun x : minstr * mem_tag => let '(_, tag) := x in color tag) H).
  + move: Hc. rewrite /get_procedures in_fset => Hc.
    have [[i tg] [Hx ->]] := in_map_In Hc.
    have [c' [Hc' Hx']] := q_in Hx. by rewrite (cc_color' Hx').
- move=> c p He. have [Hc Hp] := exp_rp He.
  apply/List.Exists_exists. exists (MrLabel (mk_entry L P C c p), Transitional.head_tag_gen PI c p).
  split; first exact: entry_cell Hc Hp. by split.
- move=> c e n m i i' tg tg' Hc Hc' He He' Hn Hm.
  have [c1 [_ H1]] := q_in (List.nth_error_In _ _ Hn).
  have [c2 [_ H2]] := q_in (List.nth_error_In _ _ Hm).
  case: (cc_in H1) => [[Et _]|[p1 [_ Ei Et]]]; first by rewrite Et in He.
  case: (cc_in H2) => [[Et' _]|[p2 [_ Ei' Et']]]; first by rewrite Et' in He'.
  subst i i' tg tg'.
  move: He He' Hc Hc' => /= He He' Hc Hc'.
  rewrite -He' in He. case: He => Ep _. subst p2 c1 c2.
  exact: uniq_label_pos q_uniq Hn Hm.
- by rewrite /= domm_map HIB.
- move=> c Hc. have [b Hb] := Hreq Hc. exists b.
  rewrite /= mapmE. move: Hb. case: (B c) => [r|] //=. rewrite mapmE.
  case: (r b) => [buf|] //=. by case: buf.
- by [].
Qed.

Lemma rp_low : lin_output_wf q.
Proof.
split.
- move=> i tg /q_in [c [_ H]]. by case: (cc_in H) => [[-> _]|[p [_ _ ->]]].
- move=> i tg /q_in [c [Hc H]]. by rewrite (cc_color' H).
- move=> n r l tg Hn.
  have [c [Hc H]] := q_in (List.nth_error_In _ _ Hn).
  case: (cc_in H) => [[_ Hi]|[p [_ Ei _]]]; last by [].
  have Hb : l \in bnzs (body c) by apply: (in_pmap_intro Hi).
  exact: clabs_findopt (q_clabs Hc (bnzs_body Hb)).
- apply: findopt_notIn_None => -[i tg] Hx. rewrite /is_label_def /=.
  case: i Hx => // l Hx. apply/eqP => E. subst l.
  have [c [Hc H]] := q_in Hx.
  have [o|o] := clabs_owned (Hok Hc) (clabs_intro H).
  + case: o => j [_ E]. exact: mk_body_neq_alloc (esym E).
  + case: o => p [_ E]. exact: mk_entry_neq_alloc (esym E).
- move=> i1 t1 i2 t2 e1 e2 /q_in [c1 [_ H1]] /q_in [c2 [_ H2]] Hcol He1 He2 Ee.
  case: (cc_in H1) => [[Et _]|[p1 [_ _ Et]]]; first by rewrite Et in He1.
  case: (cc_in H2) => [[Et' _]|[p2 [_ _ Et']]]; first by rewrite Et' in He2.
  subst t1 t2. move: Hcol He1 He2 Ee => /= Hcol [<-] [<-] /= Ep. by subst.
- have [s Es] : exists s : seq nat, s = domm I by exists (domm I).
  rewrite Ecode -Es.
  case/lastP: s Es => [|s c] Es; first by left.
  right.
  have [l El] : exists l, Tl L P C PB t c = rcons l MrHalt.
  { exists (MrLabel (rp_lab L c 3)
            :: rp_init L t c (rp_addr PB c) 2 ++ rp_push ++ rp_goto L c 0
               ++ rp_disp L c (rp_addr PB c) (size (rp_events t c))
               ++ flatten [seq rp_case L P C c ke
                            | ke <- zip (iota 0 (size (rp_events t c))) (rp_events t c)]).
    by rewrite Tl_eq -cats1 cat_cons -!catA. }
  exists (def_mem_tag c true).
  rewrite map_rcons flatten_rcons (cc_split L P C PI PB t) El /rp_tagged map_rcons.
  rewrite -!cats1 !catA size_cat /= addn1 subn1 /=.
  rewrite -[size _]addn0 nth_error_cat_r. by [].
Qed.

Lemma rp_wfmp : wf_mp L P C PI q.
Proof.
split.
- exact: rp_wf.
- exact: rp_low.
- move=> n l tg Hn.
  have [c [Hc H]] := q_in (List.nth_error_In _ _ Hn).
  have [HC _ HP] := Hok Hc.
  case: (clabs_owned (Hok Hc) (clabs_intro H)) => [[j [Hj E]]|[p [Hp E]]].
  + left. exists c, j. by split.
  + right. exists c, p. by split.
- move=> n l tg Hn Hal Hnf.
  have [c [Hc H]] := q_in (List.nth_error_In _ _ Hn).
  case: (cc_in H) => [[Et Hi]|[p [_ Ei _]]]; last by [].
  have Hj : l \in jals (body c) by apply: (in_pmap_intro Hi).
  case: (jals_body Hj) => [Hl|Ea|[P' [z [C' [Hin El]]]]].
  + have [m Hm] := clabs_findopt (q_clabs Hc Hl). by rewrite Hm in Hnf.
  + by [].
  + have [_ Hne Hent] := Hcalls Hin.
    exists C', P'. rewrite Et /=. split=> //.
    move: Hent. rewrite /= mem_filter => /andP [Hal' _].
    move: Hal'. case EC': (PI C') => [i|] //=. case Ec: (PI c) => [i'|] //= /andP [_ Him].
    exists i'. split=> //. by rewrite /Program.has_component -(HI Hc).
- move=> c p He. have [Hc Hp] := exp_rp He.
  have Hpl : is_label_def (mk_entry L P C c p)
               (MrLabel (mk_entry L P C c p), Transitional.head_tag_gen PI c p) = true.
  { by rewrite /is_label_def /= eqxx. }
  have [m Hm] := findopt_In_ex (entry_cell Hc Hp) Hpl. by rewrite Hm.
- move=> c p m i tg HC HP Hf Hm.
  have [x [Hx Hpx]] := findopt_nth Hf. rewrite Hm in Hx. case: Hx => Ex. subst x.
  move: Hpx. rewrite /is_label_def /=. case: i Hm => // l Hm /eqP El. subst l.
  have [c' [Hc' H]] := q_in (List.nth_error_In _ _ Hm).
  have [HC' HL' HP'] := Hok Hc'.
  case: (cc_in H) => [[_ Hi]|[p' [Hp' Ei Et]]].
  + have Hl : mk_entry L P C c p \in ilabs (body c') by apply: (in_pmap_intro Hi).
    have [j [Hj E]] := ilabs_body Hl.
    exfalso. exact: (mk_body_entry_disjoint HC' (leq_trans Hj HL') (esym E)).
  + case: Ei => Ei. have [E1 E2] := mk_entry_inj HP (HP' _ (in_mem_seq Hp')) Ei.
    by subst.
- move=> c Hc. by have [HC _ _] := Hok Hc.
- move=> c p He. have [Hc Hp] := exp_rp He. have [_ _ HP] := Hok Hc. exact: HP.
- move=> i tg e Hin He. have [c [_ H]] := q_in Hin.
  case: (cc_in H) => [[Et _]|[p [_ _ Et]]]; first by rewrite Et in He.
  subst tg. case: He => <-. by [].
Qed.

End Prog.

End Wf.

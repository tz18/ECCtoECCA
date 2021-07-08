Require Import core typing.
Require Import equiv_lemmas.
Require Import continuations.
Require Import String. 

Open Scope ECCA_scope.

Lemma het_compose_val (K: cont) (M: exp): isVal M -> het_compose K M = fill_hole M K.
Proof.
intros. inversion H; rewrite het_compose_equation; auto.
Qed.

Hint Resolve het_compose_val. 

Lemma het_compose_comp (K: cont) (M: exp): isComp M -> het_compose K M = fill_hole M K.
Proof.
intros. inversion H; auto; rewrite het_compose_equation; auto.
Qed.
Hint Rewrite het_compose_comp.

Lemma het_compose_hole (M: exp): het_compose Hole M = M.
Proof. induction M using term_ind; try (rewrite het_compose_equation; auto; fail).
+ rewrite het_compose_equation. rewrite H. names. tauto.
+ rewrite het_compose_equation. rewrite IHM2. rewrite IHM3. tauto.
Qed.
Hint Rewrite het_compose_hole.

Lemma fill_hole_comp_preserves_conf (e: exp) (K: cont) : cont_is_ANF K -> isComp e -> 
isConf (fill_hole e K).
Proof.
intros. destruct K; cbn; auto.
Qed.
Hint Resolve fill_hole_comp_preserves_conf.

Lemma shift_cont_ANF (K: cont):
cont_is_ANF K ->
forall x, cont_is_ANF (shift_cont x K).
Proof.
intros. destruct K. cbn. auto. names. apply shift_conf. auto.
Qed.
Hint Resolve shift_cont_ANF.

Lemma het_compose_preserves_ANF:
let P (e: @exp 0) (i: isVal e):= forall K, (cont_is_ANF K -> isConf (het_compose K e)) in
let P0 (e: @exp 0) (i: isConf e):= forall K, (cont_is_ANF K -> isConf (het_compose K e)) in
let P1 (e: @exp 0) (i: isComp e):= forall K, (cont_is_ANF K -> isConf (het_compose K e)) in
  (forall (e: @exp 0) (i: isVal e), P e i)
  /\
  (forall (e: @exp 0) (i: isConf e), P0 e i)
  /\
  (forall (e: @exp 0) (i: isComp e), P1 e i).
Proof.
intros. 
induction ANF_val_conf_comp_comb with (P:=P) (P0:=P0) (P1:=P1); auto.
1-9,12-16: unfold P, P0, P1; intros; rewrite het_compose_comp; auto; 
  apply fill_hole_comp_preserves_conf; auto.
+ unfold P1, P0. intros. rewrite het_compose_equation. apply Let; auto. 
  apply close_ANF_iff. unfold shift_cont. destruct K.
  - apply H0; cbn; auto.
  - apply H0; cbn; apply shift_conf; cbn; auto.
+ unfold P, P0. intros. rewrite het_compose_equation. apply If; auto. 
Qed.
Hint Resolve het_compose_preserves_ANF.

Lemma het_compose_preserves_conf (e: @exp 0) (i: isConf e): 
forall K, (cont_is_ANF K -> isConf (het_compose K e)).
Proof.
intros. pose het_compose_preserves_ANF. destruct a. destruct H1. apply H1; auto. 
Qed.
Hint Resolve het_compose_preserves_conf.

Lemma cont_compose_preserves_ANF (K K': cont):
cont_is_ANF K -> cont_is_ANF K' -> cont_is_ANF (cont_compose K K').
Proof. intros. unfold cont_is_ANF in *. destruct K; destruct K'.
+ auto.
+ cbn. apply close_ANF_iff. rewrite het_compose_hole. apply open_ANF_iff. auto.
+ auto.
+ cbn. apply close_ANF_iff. apply het_compose_preserves_conf. apply open_ANF_iff. auto.
  cbn. apply shift_conf. auto.
Qed.
Hint Resolve cont_compose_preserves_ANF.


Lemma cont_compose_fill_het_compose (x: name) (K K' : cont) (N : exp) (PN: isComp N) (PK: cont_is_ANF K) (PK': cont_is_ANF K'):
  (het_compose K (fill_hole N K')) = (fill_hole N (cont_compose K K')).
Proof.
  intros. destruct K'.
+  cbn. rewrite het_compose_comp; auto.
+  cbn. rewrite het_compose_equation. auto.
Qed. 
Hint Rewrite cont_compose_fill_het_compose.

Require Import Coq.Program.Equality.

Open Scope string.

Lemma let_over_branches (v M1 M2: exp) (iV: isVal v) (B: exp):
forall g,
(Equiv g (eIf v (eLet M1 B) (eLet M2 B)) (eLet (eIf v M1 M2) B)).
Proof. intros. apply aE_Trans with (M' := (eIf v (bind M1 B) (bind M2 B))).
 + apply aE_Step with (e := (eIf v (bind M1 B) (bind M2 B))).
  - auto.
  - auto.
 + apply aE_Trans with (M' := (eIf v (bind (eIf v M1 M2) B) (bind (eIf v M1 M2) B))).
  - apply aE_If with (p:="eqIf"); auto.
    * apply aE_Subst. apply aE_Symm. apply aE_If_EtaTru with (p:=free "eqIf"). auto with contexts.
    * apply aE_Subst. apply aE_Symm. apply aE_If_EtaFls with (p:=free "eqIf"). auto with contexts.
  - apply aE_Trans with (M' := bind (eIf v M1 M2) B).
    * apply aE_If2.
    * eauto.
Qed.


Lemma IH_naturality_if (g: env) (K : cont) (iK: cont_is_ANF K) 
(v: exp) (iV: isVal v) (m1 m2 : exp) (iM1: isConf m1) (iM2: isConf m2)
(y: name):
  (Equiv (g & y ~ Assum (eEqv v eTru)) (het_compose K m1) (fill_hole m1 K)) ->
  (Equiv (g & y ~ Assum (eEqv v eFls)) (het_compose K m2) (fill_hole m2 K)) -> 
  (Equiv g (eIf v (het_compose K m1) (het_compose K m2)) (eIf v (fill_hole m1 K) (fill_hole m2 K))).
Proof.
intros. eapply aE_If; auto.
+ apply H.
+ apply H0.
Qed.

Lemma IH_naturality_let (g: env) (K : cont) (iK: cont_is_ANF K) 
(n: exp) (iN: isComp n) (m: exp) (iM : isConf m) (A: exp) (x: name):
  (Equiv (g & x ~ Def n A) (het_compose (shift_cont x K) (open x m)) (fill_hole (open x m) (shift_cont x K))) ->
  (Equiv g ((eLet n (close x (het_compose (shift_cont x K) (open x m))))) (eLet n (close x (fill_hole (open x m) (shift_cont x K))))).
Proof.
intros. eapply aE_Let; auto.
+ names. apply H.
Qed.

(* As seen in the paper!*)
Theorem naturality (M : exp) (iM: isConf M):
  forall (K : cont) (iK: cont_is_ANF K) (G : env), (G  ⊢ (het_compose K M) ≡ (fill_hole M K))%ECCA.
Proof.
  induction M using term_ind.
1-8,10-11,13-16: intros; inversion iM; rewrite het_compose_comp; auto.
  + inversion iM; subst. destruct K.
    - cbn. rewrite het_compose_hole. auto.
    - intros. rewrite het_compose_equation. clear IHM1. eapply aE_Trans.
      * eapply IH_naturality_let with (g:= G) (x:="k") (n:= M1) (m:= M2) (K:= (LET [⋅] in B)) (A:= eUni uProp); auto. names. eapply H.
        ++ apply open_conf. auto.
        ++ cbn. cbn in iK. apply shift_conf. auto.
      * names. apply aE_Step with (e := (bind (bind M1 M2) B)).
        { apply R_Trans with (e':= eLet (bind M1 M2) B) .
          { apply R_Trans with (e':= (bind M1 (eLet M2 (wk B)))).
            { apply R_RedR. apply st_Let. }
            { names. apply R_Reflex. }}
          { apply R_RedR. apply st_Let. }}
        {
          apply R_Trans with (e' := (eLet (bind M1 M2) B)).
          {
            apply R_CongLet with (x:="x") (A:=eUni uProp).
            { apply R_RedR. apply st_Let. }
            { apply R_Reflex. }
          }
          apply R_RedR. apply st_Let.
        }
     - inversion H0. inversion H1.
  + intros; inversion iM; subst. destruct K.
    - rewrite het_compose_hole. auto.
    - rewrite het_compose_equation. cbn. rewrite IH_naturality_if with (y:="y"); auto. cbn. apply let_over_branches; auto.
    - inversion H. inversion H0.
Qed.
Hint Resolve naturality.

Open Scope ECCA.
Require Setoid.
Lemma total_renamings_distribute_het_compose (B: exp) :
      forall (K: cont) (r: ren) (t: total r), [r] (K 《 B 》) = (rename_cont r K )《[r]B》%ECCA.
Proof.
induction B using term_ind. 
2,3,4,5,6,7,8,10,11,13-16: intros; rewrite het_compose_equation; rewrite het_compose_equation; names; destruct K; cbn; auto.
+ intros. destruct K. 
  - rewrite het_compose_hole. cbn. rewrite applyt_is_applyv with (rn:= t). names. rewrite het_compose_equation. cbn. auto.
  - intros. rewrite het_compose_equation. rewrite het_compose_equation. names. 
  cut (applyv r v = eId (applyt r t v)).
  * intros. rewrite H. names. rewrite <- applyt_is_applyv. auto.
  * names. rewrite <- applyt_is_applyv. auto.
+ intros. cbn. rewrite het_compose_equation. rewrite het_compose_equation. rewrite het_compose_equation. rewrite <- het_compose_equation.
  names. rewrite H.
  destruct K. all: names; auto.
+ intros. cbn. repeat rewrite het_compose_equation. rewrite <- het_compose_equation. rewrite <- het_compose_equation. rewrite <- het_compose_equation. rewrite <- het_compose_equation.  cbn. rewrite IHB2; auto. rewrite IHB3; auto.
Qed.

Lemma total_renamings_distribute_cont_compose (K K': cont):
forall (r: ren) (t: total r), 
      (rename_cont r (cont_compose K' K)) =
      (cont_compose (rename_cont r K') (rename_cont r K)).
Proof.
intros. destruct K, K'; auto.
+ names. repeat rewrite het_compose_hole. auto.
+ cbn. names. rewrite total_renamings_distribute_het_compose. names. auto.
  auto.
Qed. 

Lemma shift_over_conts (K K': cont):
      (cont_compose (shift_cont "k" K') (shift_cont "k" K)) = 
      (shift_cont "k" (cont_compose K' K))%ECCA.
Proof. unfold shift_cont.
rewrite total_renamings_distribute_cont_compose; cbn; auto.
Qed.


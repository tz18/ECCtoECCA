Require Import core core_lemmas typing.
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
1-9,12-14: unfold P, P0, P1; intros; rewrite het_compose_comp; auto; 
  apply fill_hole_comp_preserves_conf; auto.
+ unfold P1, P0. intros. rewrite het_compose_equation. apply Let; auto. 
  apply close_ANF_iff. unfold shift_cont. destruct K.
  - apply H0; try apply open_ANF_iff; auto.
  - apply H0; try apply open_ANF_iff; auto.
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
  cbn. apply open_ANF_iff. apply wk_ANF_iff. auto.
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
(*didn't use*)
(* Lemma K_compat (g: env) (K : cont) (e1 e2 : exp) (A: @exp 0):
  (RedClos g e1 e2) ->
  (Equiv g (fill_hole e1 K)) (fill_hole e2 K).
Proof.
  intros. destruct K.
  + simpl. eapply aE_Step. apply H. apply R_Refl.
  + simpl. eapply aE_Step.
     - eapply R_CongLet with (x:="x") (A:=A). (*TODO: This A is arbitrary...*)
       * apply H.
       * apply R_Refl.
     - apply R_Refl.
Qed. *)

(*Lemma bind_commutes_over_fill_hole (g: env) (K : cont) (n m : exp):
  (Equiv g (bind n (fill_hole m wk_cont K))) (fill_hole (bind n m) K).
Proof.
  destruct K.
  + simpl. eapply aE_Step; apply R_Refl.
  + simpl.
    assert (Equiv g (eLet (bind n m) B) (bind (bind n m) B)).
    * eapply aE_Step. apply R_RedR. apply R_Let. apply R_Refl.
    * apply equiv_sym. eapply equiv_trans. apply H. apply equiv_sym.
      (*don't think bind (bind n m) B = (bind n (bind m B)) *)
Admitted.*)

Lemma let_over_branches (v M1 M2: exp) (iV: isVal v) (B: exp):
forall g,
(Equiv g (eIf v (eLet M1 B) (eLet M2 B)) (eLet (eIf v M1 M2) B)).
Proof. intros. apply aE_Trans with (M' := (eIf v (bind M1 B) (bind M2 B))).
 + apply aE_Step with (e := (eIf v (bind M1 B) (bind M2 B))).
  - auto.
  - auto.
 + apply aE_Trans with (M' := (eIf v (bind (eIf v M1 M2) B) (bind (eIf v M1 M2) B))).
  - apply aE_If with (x:="eqIf"); auto.
    * apply aE_Subst. apply aE_Symm. apply aE_If_EtaTru with (x:=free "eqIf"). names. auto.
    * apply aE_Subst. apply aE_Symm. apply aE_If_EtaFls with (x:=free "eqIf"). names. auto.
  - apply aE_Trans with (M' := bind (eIf v M1 M2) B).
    * apply aE_If2.
    * eauto.
Qed.


Lemma IH_naturality_if (g: env) (K : cont) (iK: cont_is_ANF K) 
(v: exp) (iV: isVal v) (m1 m2 : exp) (iM1: isConf m1) (iM2: isConf m2)
(y: name):
  (Equiv (g & y ~ Eq v eTru) (het_compose K m1) (fill_hole m1 K)) ->
  (Equiv (g & y ~ Eq v eFls) (het_compose K m2) (fill_hole m2 K)) -> 
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

(*1. Zeta reduction on the left. 
2. IH (rewrite K<<M''>> to K[M] on the left. 
3. On the right, use K_compat lemma, should have goal K[M][x :=n] \equiv K[M[x := n]] 
e -> e', then K[e] = K[e'] 
3. Have goal: Show K[M'][x := n] \equiv K[let x = n in M'] 
4. need lemma to show K[M][x :=n] \equiv K[M[x := n] *)

Theorem naturality (M : exp) (iM: isConf M):
  forall (K : cont) (iK: cont_is_ANF K) (G : env), (G |- (het_compose K M) =e= (fill_hole M K))%ECCA.
Proof.
  induction M using term_ind.
1-8,10-11,13-14: intros; inversion iM; rewrite het_compose_comp; auto.
  + inversion iM; subst. destruct K.
    - cbn. rewrite het_compose_hole. auto.
    - intros. rewrite het_compose_equation. clear IHM1. eapply aE_Trans.
      * eapply IH_naturality_let with (g:= G) (x:="k") (n:= M1) (m:= M2) (K:= (LET [] in B)) (A:= eUni uProp); auto. names. eapply H.
        ++ apply open_conf. auto.
        ++ cbn. cbn in iK. apply shift_conf. auto.
      * names. apply aE_Step with (e := (bind (bind M1 M2) B)).
        { apply R_Trans with (e':= eLet (bind M1 M2) B) .
          { apply R_Trans with (e':= (bind M1 (eLet M2 (wk B)))).
            { apply R_RedR. apply R_Let. }
            { names. apply R_Refl. }}
          { apply R_RedR. apply R_Let. }}
        {
          apply R_Trans with (e' := (eLet (bind M1 M2) B)).
          {
            apply R_CongLet with (x:="x") (A:=eUni uProp).
            { apply R_RedR. apply R_Let. }
            { apply R_Refl. }
          }
          apply R_RedR. apply R_Let.
        }
     - inversion H0. inversion H1.
  + intros; inversion iM; subst. destruct K.
    - rewrite het_compose_hole. auto.
    - rewrite het_compose_equation. cbn. rewrite IH_naturality_if with (y:="y"); auto. cbn. apply let_over_branches; auto.
    - inversion H. inversion H0.
Qed.
Hint Resolve naturality.

Lemma shift_cont_ANF (K: cont):
cont_is_ANF K ->
forall x, cont_is_ANF (shift_cont x K).
Proof.
intros. destruct K. cbn. auto. cbn. apply open_ANF_iff. apply wk_ANF_iff. cbn in H. auto.
Qed.
Hint Resolve shift_cont_ANF.

Lemma shift_distributes_cont_compose (K K': cont):
      (cont_compose (shift_cont "k" K') (shift_cont "k" K)) = 
      (shift_cont "k" (cont_compose K' K))%ECCA.
Proof.
destruct K; destruct K'.
+ auto.
+ auto.
+ names. rewrite het_compose_hole. rewrite het_compose_hole. auto.
+ cbn. names. 
cut ((het_compose (LET [] in ([(^ "k"),, ^ "k"] B0)) ([(^ "k"),, "k"] (open "k" B)))
  = ([(^ "k"),, "k"] (het_compose (LET [] in ([^ "k"] B0)) (open "k" B)))).
  - intros. cbn in *. rewrite H. auto.
  - cbn. names. admit.
Admitted.

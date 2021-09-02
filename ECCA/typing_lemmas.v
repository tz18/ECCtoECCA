Require Export typing.
Require Import equiv_lemmas.

Open Scope ECCA_scope.

(* Broken until we fix/extend shifted names *)

Theorem SubTypes_weakening Γ A B (pT: (Γ ⊢ A ≲ B)):
  forall r Δ,
    Γ =[r]=> Δ ->
    (Δ ⊢ ([r] A) ≲ [r] B).
Proof.
induction pT; names; eauto; intros.
+ apply ST_Cong. apply Equiv_weakening with (Δ:=Δ) (r:=r) in H; auto.
+ apply ST_Pi with (x:=x). apply Equiv_weakening with (Δ:=Δ) (r:=r) in H; auto.
  names. specialize IHpT with (r:=(r,,x)%ren). apply IHpT. apply ctx_rename. auto.
+ apply ST_Sig with (x:=x); auto.
  names. specialize IHpT2 with (r:=(r,,x)%ren). apply IHpT2. apply ctx_rename. auto.
Qed.

(* vvv Not true vvv*)
(* Definition WellFormed_weakening Γ (pWF: (⊢ Γ)):=
  forall r Δ,
    Γ =[r]=> Δ ->
    (⊢ Δ). *)

Lemma Types_only_if_wellformed Γ e A:
(Γ ⊢ e : A)->
(⊢ Γ). 
Proof.
intros.
induction H; auto.
Qed.
Hint Resolve Types_only_if_wellformed.

Lemma Type_weakening Γ e A (pT: (Γ ⊢ e : A)):
  forall r Δ,
    Γ =[r]=> Δ ->
    (⊢ Δ) ->
    (Δ ⊢ ([r] e) : [r] A).
Proof. 
induction pT; auto.
all: try (intros; constructor; eauto; fail).
+ intros. names. destruct H1 eqn:H3. 
  rewrite applyt_is_applyv with (rn:=total). names. apply aT_Var.
   - eauto.
   - unfold assumes. destruct H0. 
      * apply f in H0. left. names in H0. apply H0.
      * destruct H0. apply f in H0. right. eauto. 
+ intros. names. apply aT_Sig with (x:=x). eauto.
  names. apply IHpT2 with (Δ:= (Δ & x ~ Assum ([r] A0))) (r:= (r,, x)%ren).
  apply ctx_rename; eauto. apply wf_Assum with (eUni (uType i)); eauto.
+  intros. names. apply aT_Pair with ([r] U).
  - auto.
  - specialize IHpT2 with (r:=r) (Δ:=Δ). names in IHpT2. apply IHpT2; eauto.
  - specialize IHpT3 with (r:=r) (Δ:=Δ). names in IHpT3. apply IHpT3; eauto.
+  intros. names. eapply aT_Prod_Prop with (x:=x). eauto.
  names. apply IHpT2 with (Δ:= (Δ & x ~ Assum ([r] A0))) (r:= (r,, x)%ren).
  apply ctx_rename. auto. eauto.
+  intros. names. eapply aT_Prod_Type with (x:=x). eauto.
  names. apply IHpT2 with (Δ:= (Δ & x ~ Assum ([r] A0))) (r:= (r,, x)%ren).
  apply ctx_rename. auto. eauto.
+  intros. names. eapply aT_Lam with (x:=x). eauto.
  names. apply IHpT2 with (Δ:= (Δ & x ~ Assum ([r] A0))) (r:= (r,, x)%ren).
  apply ctx_rename. auto. apply wf_Assum with ([r] U); eauto.
+  intros. names. apply aT_Let with (x:=x) (A:=([r]A0)) (U:=([r]U)); eauto.
  names. apply IHpT3 with (Δ:= (Δ & x ~ Def ([r] n) ([r] A0))) (r:= (r,, x)%ren).
  apply ctx_rename. auto. apply wf_Def with ([r] U); eauto.
+  intros. names. apply aT_If with (x:=x) (p:=p) (U:=[r,,x]U). 
  - names. apply IHpT1 with (Δ:= (Δ & x ~ Assum eBool)) (r:= (r,, x)%ren).
    apply ctx_rename. auto. eauto.
  - eauto.
  - names. specialize IHpT3 with (Δ:= (Δ & p ~ Assum (eEqv ([r] e) eTru))) (r:= (r,, p)%ren). names in IHpT3. apply IHpT3.
    apply ctx_rename. auto. eapply wf_Assum with (eUni (uType 0)). auto.
    apply aT_Equiv with (B:= eBool); eauto.
  - names. specialize IHpT4 with (Δ:= (Δ & p ~ Assum (eEqv ([r] e) eFls))) (r:= (r,, p)%ren). names in IHpT4. apply IHpT4.
    apply ctx_rename. auto. eapply wf_Assum with (eUni (uType 0)). auto.
    apply aT_Equiv with (B:= eBool); eauto.
+ intros. apply aT_Conv with (A:=[r]A0)(U:=[r]U); eauto.
  apply SubTypes_weakening with g; auto.
+  intros. names. apply aT_App with ([r]A').
  - apply IHpT1; auto.
  - apply IHpT2; auto.
+ intros. names. apply aT_Fst with ([r]B). apply IHpT; auto.
+ intros. names. apply aT_Snd with ([r]A0). apply IHpT; auto.
+ intros. names. apply aT_Refl with ([r]A0). auto.
+ intros. names. apply aT_Equiv with (B:=[r]B); eauto.
Qed.

(* Theorem weakening {Γ e A pT pWF}:
Type_weakening Γ e A pT /\ WellFormed_weakening Γ pWF.
Proof.
induction Types_WellFormed_mutind with (P:=Type_weakening) (P0:=WellFormed_weakening). auto.
all: try (intros; constructor; eauto; fail); unfold Type_weakening. *)

Lemma cons_weakening_assum (g: env) (A A': exp) (x: name):
(g ⊢ A : A') ->
  (forall B B', 
   ((g ⊢ B : B') -> 
   (g & x ~ Assum B ⊢ [^x] A : [^x] A'))).
Proof.
intros. apply Type_weakening with g; auto. apply ctx_shift; apply ctx_id.
apply wf_Assum with B'; auto. apply Types_only_if_wellformed with A A'; auto. 
Qed.

Lemma cons_weakening_def (g: env) (A A': exp) (x: name):
(g ⊢ A : A') ->
  (forall B B' e, 
   ((g ⊢ B : B') ->
    (g ⊢ e : B) ->
   (g & x ~ Def e B ⊢ [^x] A : [^x] A'))).
Proof.
intros. apply Type_weakening with g; auto. apply ctx_shift; apply ctx_id.
apply wf_Def with B'; auto. apply Types_only_if_wellformed with A A'; auto.
Qed.

Require Import String.
Open Scope string.

Lemma WF_1: 
(⊢ (ctx_empty & "x" ~ Def eBool (eUni (uType 0)))).
Proof. eapply wf_Def; auto.
Qed.

Lemma WF_2:
(⊢(ctx_empty & "x" ~ Def eBool (eUni (uType 0)) & "y" ~ Assum (eId (free "x")))).
Proof. eapply wf_Assum. apply WF_1. apply aT_Var; eauto with contexts.
Qed.

Lemma WF_3:
(⊢((((ctx_empty & "x" ~ Def eBool (eUni (uType 0))
            & "y" ~ Assum (eId (free "x")))
            & "x" ~ Def (eUni uProp) (eUni (uType 0)))))).
Proof. eapply wf_Def. apply WF_2.
  - apply aT_Ax_Type. apply WF_2.
  - apply aT_Ax_Prop. apply WF_2.
Qed.

(* Lemma typing_is_broken_part_1: 
((ctx_empty & "x" ~ Def eBool (eUni (uType 0)) & "y" ~ Assum (eId (free "x"))) ⊢ eId (free "y") : eBool).
Proof.
eapply aT_Conv.
+ apply aT_Var.
  - apply WF_2. 
  - left. auto with contexts.
+ apply aT_Bool. eapply wf_Assum.
  - eapply wf_Def.
    * auto.
    * auto.
    * auto.
  - apply aT_Var; eauto with contexts.
+ apply ST_Cong. apply aE_Step with (e:=eBool).
  - apply R_RedR. apply st_ID with (A:= (eUni (uType 0))); auto with contexts.
  - apply R_Reflex.
Qed. *)

(* Lemma typing_is_broken_part_2: 
(((ctx_empty & "x" ~ Def eBool (eUni (uType 0))
            & "y" ~ Assum (eId (free "x")))
            & "x" ~ Def (eUni uProp) (eUni (uType 0))) ⊢ eId (free "y") : (eUni uProp)).
Proof.
eapply aT_Conv.
+ apply aT_Var. apply WF_3. left. auto with contexts.
+ apply aT_Ax_Prop. apply WF_3.
+ apply ST_Cong. apply aE_Step with (e:=eUni uProp).
  - apply R_RedR. apply st_ID with (A:= (eUni (uType 0))). auto with contexts.
  - apply R_Reflex.
Qed. *)
(* Conclusion: We need to shift the bodies of ass/defs in the context when we add a new ass/def *)


Lemma WellFormed_implies_well_typed_assum (g: env):
WellFormed g ->
forall (v: var) (A: exp),
(has g v (Assum A)) ->
exists U, Types g A U.
Proof.
induction 1.
+ intros. inversion H.
+ intros. rename H0 into H2. rename H1 into H0. rename H2 into H1. 
  apply has_inversion in H0. apply get_inversion in H0.
  destruct H0. destruct H0. inversion H0. subst.
  destruct H2.
  * destruct H0 as [g']. destruct H0 as [c]. destruct H0.
    inversion H0. subst. names in H2. inversion H2. subst. destruct H0.
    exists ([^x0] U). apply cons_weakening_assum with U; auto.
  * destruct H0 as [g']. destruct H0. destruct H0 as [c]. destruct H0. destruct H0 as [c'].
    destruct H0. destruct H2. destruct H3. inversion H0. subst. clear H0.
    destruct H4. cut (has g' x2 c'). intro. cut (exists B, c' = Assum B). intro. 
    destruct H5 as [B]. subst. names in H3. inversion H3. subst.
    apply IHWellFormed in H4. destruct H4 as [B']. 
    apply cons_weakening_assum with (A:=B) (A':=B')(x:=x1) in H1.
    eauto. eauto. unfold apply in H3. destruct c'. eauto. discriminate.
    unfold has. rewrite H0. auto.
+ intros. apply has_inversion in H2. apply get_inversion in H2.
  destruct H2. destruct H2. destruct H3.
  * destruct H3. destruct H3. destruct H3.
    inversion H3. subst. inversion H4.
  * destruct H3 as [g']. destruct H3. destruct H3 as [c]. destruct H3.
    destruct H3 as [c']. destruct H3. destruct H4. destruct H5.
    inversion H3. subst. clear H3.
    cut (has g' x2 c'). cut (exists B, c' = Assum B). intros.
    destruct H2 as [B]. subst. names in H6. inversion H6. subst.
    apply IHWellFormed in H3. destruct H3 as [B'].
    apply cons_weakening_def with (A:=B) (A':=B') (B':=U)(x:=x1) in H1.
    all: eauto. unfold apply in H6. destruct c'. eauto. discriminate. unfold has. rewrite H5. auto.
Qed.

Lemma WellFormed_implies_well_typed_def (g: env):
WellFormed g ->
forall (v: var) (A: exp) (e: exp),
(has g v (Def e A)) ->
exists U, Types g A U.
Proof.
induction 1.
+ intros. inversion H.
+ intros. rename H0 into H2. rename H1 into H0. rename H2 into H1. 
  apply has_inversion in H0. apply get_inversion in H0.
  destruct H0. destruct H0. inversion H0. subst.
  destruct H2.
  * destruct H0. destruct H0. destruct H0. inversion H0. subst. inversion H2. 
  * destruct H0 as [g']. destruct H0. destruct H0 as [c]. destruct H0. destruct H0 as [c'].
    destruct H0. destruct H2. destruct H3. inversion H0. subst. clear H0.
    destruct H4. cut (has g' x2 c'). intro. cut (exists e' B, c' = Def e' B). intro. 
    destruct H5 as [e']. destruct H5 as [B]. subst. names in H3. inversion H3. subst.
    apply IHWellFormed in H4. destruct H4 as [B']. 
    apply cons_weakening_assum with (A:=B) (A':=B')(x:=x1) in H1.
    eauto. eauto. unfold apply in H3. destruct c'. discriminate. eauto.
    unfold has. rewrite H0. auto.
+ intros. apply has_inversion in H2. apply get_inversion in H2.
  destruct H2. destruct H2. destruct H3.
  * destruct H3 as [g']. destruct H3 as [c]. destruct H3.
    inversion H3. subst. names in H4. inversion H4. subst. destruct H4.
    exists ([^x0] U). apply cons_weakening_def with U; auto.
  * destruct H3 as [g']. destruct H3. destruct H3 as [c]. destruct H3. destruct H3 as [c'].
    destruct H3. destruct H4. destruct H5. inversion H3. subst. clear H3.
    cut (has g' x2 c'). intro. cut (exists e' B, c' = Def e' B). intro. 
    destruct H3 as [e']. destruct H3 as [B]. subst. names in H6. inversion H6. subst.
    apply IHWellFormed in H2. destruct H2 as [B']. exists ([^x1] B').
    apply cons_weakening_def with (A:=B) (A':=B')(x:=x1) (B':=U); eauto.
    unfold apply in H6. destruct c'. discriminate. eauto.
    unfold has. rewrite H5. auto.
Qed.

Lemma type_well_typed (g: env) (N: exp) (A: exp) :
  (g ⊢ N : A) ->
  exists U , Types g A (eUni (uType i)).
Proof.
  induction 1; eauto.
  - intros. destruct H0.
    + apply WellFormed_implies_well_typed_assum with (v:=x); auto.
    + destruct H0 as [e]. apply WellFormed_implies_well_typed_def with (v:=x) (e:=e); auto.
  -  
  
  Admitted. (*  apply WellFormed_implies. intros. induction H0.
    + subst. destruct H; destruct h. 
    + subst. destruct H. cbn in h. destruct (bindv (closev x0 x)).
      * names.  
  - exists (eUni (uType 1)). apply aT_Ax_Type. auto.
  - exists (eUni (uType 0)). apply aT_Bool. auto.
  - exists (eUni (uType 0)). apply aT_Bool. auto.
  - apply IHTypes1.
  - exists (eUni (uType 0)). eapply aT_Sig. shelve. shelve.
  - exists (eUni (uType 0)). apply aT_Ax_Prop. shelve.
  - exists (eUni (uType (S i))). apply aT_Ax_Type. shelve.
  - exists (eUni (uProp)). eapply aT_Prod_Prop. shelve. shelve.
  - shelve.
  - shelve.
  - exists U. auto.
  - shelve.
  - shelve.
  - shelve. 
Admitted.  *)

Lemma has_type_wf_g (g: env) (N: exp) (A: exp) (x : name):
  Types g N A ->
  WellFormed g ->
  WellFormed (g & x ~ (Def N A)).
Proof.
  intros.  apply type_well_typed in H as H1; auto. destruct H1.
  apply wf_Def with (U := x0); auto.
Qed.  *)
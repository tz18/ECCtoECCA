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

Definition Type_weakening Γ e A (pT: (Γ ⊢ e : A)):=
  forall r Δ,
    Γ =[r]=> Δ ->
    (Δ ⊢ ([r] e) : [r] A).

Definition WellFormed_weakening Γ (pWF: (⊢ Γ)):=
  forall r Δ,
    Γ =[r]=> Δ ->
    (⊢ Δ).

Theorem weakening {Γ e A pT pWF}:
Type_weakening Γ e A pT /\ WellFormed_weakening Γ pWF.
Proof.
induction Types_WellFormed_mutind with (P:=Type_weakening) (P0:=WellFormed_weakening). auto.
all: try (intros; constructor; eauto; fail); unfold Type_weakening.
+ intros. names. destruct H0 eqn:H3. 
  rewrite applyt_is_applyv with (rn:=total). names. apply aT_Var.
   - eauto.
   - unfold assumes. destruct a. 
      * apply f in H1. left. names in H1. apply H1.
      * destruct H1. apply f in H1. right. eauto.
+ intros. names. apply aT_Sig with (x:=x). eauto.
  names. apply H0 with (Δ:= (Δ & x ~ Assum ([r] A0))) (r:= (r,, x)%ren).
  apply ctx_rename. auto.
+  intros. names. apply aT_Pair.
  - auto.
  - specialize H0 with (r:=r) (Δ:=Δ). names in H0. apply H0. eauto.
+  intros. names. eapply aT_Prod_Prop with (x:=x). eauto.
  names. apply H0 with (Δ:= (Δ & x ~ Assum ([r] A0))) (r:= (r,, x)%ren).
  apply ctx_rename. auto.
+  intros. names. eapply aT_Prod_Type with (x:=x). eauto.
  names. apply H0 with (Δ:= (Δ & x ~ Assum ([r] A0))) (r:= (r,, x)%ren).
  apply ctx_rename. auto.
+  intros. names. eapply aT_Lam with (x:=x). eauto.
  names. apply H with (Δ:= (Δ & x ~ Assum ([r] A0))) (r:= (r,, x)%ren).
  apply ctx_rename. auto.
+  intros. names. eapply aT_Let with (x:=x). eauto.
  names. apply H0 with (Δ:= (Δ & x ~ Def ([r] n) ([r] A0))) (r:= (r,, x)%ren).
  apply ctx_rename. auto.
+  intros. names. eapply aT_If with (x:=x). 
  - names. apply H with (Δ:= (Δ & x ~ Assum eBool)) (r:= (r,, x)%ren).
    apply ctx_rename. auto.
  - eauto.
  - names. specialize H1 with (Δ:= (Δ & p ~ Assum (eEqv ([r] e0) eTru))) (r:= (r,, p)%ren). names in H1. apply H1.
    apply ctx_rename. auto.
  - names. specialize H2 with (Δ:= (Δ & p ~ Assum (eEqv ([r] e0) eFls))) (r:= (r,, p)%ren). names in H2. apply H2.
    apply ctx_rename. auto.
+  intros. apply aT_Conv with (A:=[r]A0)(U:=[r]U); eauto.
  apply SubTypes_weakening with g; auto.
+  intros. names. apply aT_App with ([r]A').
  - apply H. auto.
  - apply H0. auto.
+ intros. names. apply aT_Fst with ([r]B). apply H. auto.
+ intros. names. apply aT_Snd with ([r]A0). apply H. auto.
+ intros. names. apply aT_Refl with ([r]A0). auto.
+ unfold WellFormed_weakening. intros.  


Lemma weakening1 (g: env) (A U B: exp) (x: name):
(g ⊢ A : U) ->
(g & x ~ Assum B ⊢ [^x] A : U) /\ (forall e: exp, (g & x ~ Def e B ⊢ [^x] A : U)).
Proof.
Admitted.

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

Lemma typing_is_broken_part_1: 
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
Qed.

Lemma typing_is_broken_part_2: 
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
Qed.


(* Conclusion: We need to shift the bodies of ass/defs in the context when we add a new ass/def *)

Lemma WellFormed_implies (g: env) (A: exp):
WellFormed g ->
forall (x: name),
assumes g (free x) A ->
exists U, Types g ([^x]A) U.
Proof.
induction g. 
 - intros. inversion H0. inversion H1. inversion H1. inversion H2.
 - intros. inversion H. subst. inversion H0.
   cbn in H1. destruct (closev a (free x)). Admitted.
   


(* H1.
  + cbn in H1. destruct (bindv (closev x (free x0))).
    * cut (assumes g v A).
      -- intros. cut (exists n, v = free n).
         ** intros. destruct H3. subst. apply IHWellFormed in H2. destruct H2. exists x2. apply weakening1. auto. 
      -- auto.
    * inversion H1. subst. exists U. apply weakening1. auto.
  + cbn in H1. destruct (bindv (closev x x0)).
    * cut (assumes g v A).
      -- intros. apply IHWellFormed in H2. destruct H2. exists x1. apply weakening1. auto. 
      -- auto.
    * inversion H1. inversion H2.
  - intros. destruct H2.
    + cbn in H2. destruct (bindv (closev x x0)).
      * cut (assumes g v A).
        -- intros. apply IHWellFormed in H3. destruct H3. exists x1. apply weakening1. auto. 
        -- auto.
      * inversion H2.
    + cbn in H2. destruct (bindv (closev x x0)).
      * cut (assumes g v A).
        -- intros. apply IHWellFormed in H3. destruct H3. exists x1. apply weakening1. auto. 
        -- auto.
      * inversion H2. inversion H3. subst. exists U. apply weakening1. auto.
Qed. *)



Lemma type_well_typed (g: env) (N: exp) (A: exp) :
  (g ⊢ N : A) ->
  exists U , Types g A U.
Proof.
  induction 1.
  - exists (eUni (uType 1)). apply aT_Ax_Type. auto.
  - exists (eUni (uType (S (S i)))). apply aT_Ax_Type. auto.
  - intros. Admitted. (*  apply WellFormed_implies. intros. induction H0.
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
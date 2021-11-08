Require Export equiv.
Require Import reduction_lemmas.
Require Import Equivalence.

Lemma Equiv_weakening:
forall (Γ: context) (e1 e2: exp),
(Γ ⊢ e1 ≡ e2) -> 
forall (Δ: context) (r: ren), 
Γ =[r]=> Δ ->
(Δ ⊢ ([r] e1) ≡ ([r] e2)).
Proof. induction 1; cbn; auto.
+ intros. apply aE_Step with (e:=[r]e); eauto using Reduces_weakening.
+ intros.
  names. destruct H0. eapply aE_Reflect with (x:= applyt s _ x).
  apply H0 in H. names in H. apply H.
+ intros; names; auto.
+ intros. apply aE_Trans with (M':=[r]M'); auto.
+ intros. apply aE_Lam with (x:= x). auto. names. apply IHEquiv2.
  auto. apply ctx_rename. auto.
+ intros. apply aE_Eta with (x:= x) (A:=[r] A) (F':= [r] F') (F:=[r] F) (G:= [r] G) (G':=[r] G'). eauto using IHEquiv1. 
  eauto using IHEquiv2. specialize IHEquiv3 with (Δ:= (Δ & x ~ Assum ([r] A))) (r:= (r,, x)%ren).
  names in IHEquiv3. names. cut ((@open x 0 (applyv r (closev x (free x)))) = (eId (free x))). 
  - intro. rewrite H3 in IHEquiv3. apply IHEquiv3. apply ctx_rename. auto.
  - names. auto.
+ intros. apply aE_Pi with (x:= x). auto. names. apply IHEquiv2.
  auto. apply ctx_rename. auto.
+ intros. apply aE_Sig with (x:= x). auto. names. apply IHEquiv2.
  auto. apply ctx_rename. auto.
+ intros. apply aE_Let with (x:= x) (A:= [r] A). auto. names. apply IHEquiv2.
  auto. apply ctx_rename. auto.
+ intros. apply aE_If with (p:=p). auto.
  - specialize IHEquiv2 with (Δ:= (Δ & p ~ (Eqv ([r] V) eTru))) (r:=(r,, p)%ren). names. names in IHEquiv2. apply IHEquiv2.
    apply ctx_rename. auto.
  - specialize IHEquiv3 with (Δ:= (Δ & p ~ (Eqv ([r] V) eFls))) (r:=(r,, p)%ren). names. names in IHEquiv3. apply IHEquiv3.
    apply ctx_rename. auto.
+ intros. destruct H0. apply aE_If_EtaTru with (p:=applyt s total p).
  apply H0 in H. names in H. apply H.
+ intros. destruct H0. apply aE_If_EtaFls with (p:=applyt s total p).
  apply H0 in H. names in H. apply H.
Qed.
 
Lemma Equiv_cons_shift:
    forall (Γ : context) (e1 e2: exp) (A: ctxmem) (x: name),
      Equiv Γ e1 e2 -> Equiv (Γ & x ~ A) ([^x] e1) ([^x] e2).
Proof. intros.
apply Equiv_weakening with (Γ:= Γ). auto. apply ctx_shift. apply ctx_id.
Qed.

Lemma equiv_refl (g: env): Reflexive (Equiv g).
Proof.
unfold Reflexive. intros. eapply aE_Reflex. 
Qed.

Lemma equiv_sym (g: env): Symmetric (Equiv g).
Proof.
  unfold Symmetric. intros. eapply aE_Symm. auto.
Qed.

Lemma equiv_trans (g: env): Transitive (Equiv g).
Proof.
  unfold Transitive. intros. eapply aE_Trans. apply H. auto.
Qed.

Instance Equiv_equiv (g: env) : Equivalence (Equiv g).
Proof.
split. apply equiv_refl. apply equiv_sym. apply equiv_trans.
Qed.
Hint Rewrite Equiv_equiv.
Require Import String.



(*TODO: To use this, we need to declare some functions proper wrt to equiv.
Then we can do rewriting. 
See page 17 of 
https://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf *)


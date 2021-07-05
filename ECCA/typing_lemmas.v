Require Export typing.

Open Scope ECCA_scope.
Theorem weakening {Γ e A}:
  (Γ ⊢ e : A) ->
  forall r Δ,
    Γ =[r]=> Δ ->
    (Δ ⊢ ([r] e) : A).
Proof.
Admitted.

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
  (⊢ g) ->
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
Qed. 
Require Export ECCA_typing.
Require Export ECCA_equiv.
Require Export ECCA_continuations.
Require Export ECCA_het_comp.

Lemma Cut (g: ECCAenv) (K : cont) (N: ECCAexp) (A B: ECCAexp):
(ECCA_cont_has_type g K (Cont N A B) ->
ECCA_has_type g N A ->
ECCA_has_type g (fill_hole N K) B)%ECCA.
Proof. 
intros. inversion H ; subst ; cbv.
- assumption. 
- cut (@bind N 0 (@wk 0 B) = B); simpl_term_eq. 
  intros. rewrite <- H1. eapply aT_Let with (n:= N) (m:= M) (A:=A) (B:=(wk B)) (x:=y) (g:=g); assumption.
Qed.

Lemma weakening (g : ECCAenv) (x : name) (N A A' : ECCAexp):
  ECCA_has_type g N A ->
  ECCA_has_type (ctx_cons g x (Assum A')) N A.
Proof.
Admitted.

Lemma def_weakening (g : ECCAenv) (x : name) (N N' A A' : ECCAexp):
  ECCA_has_type g N A ->
  ECCA_has_type (ctx_cons g x (Def N' A')) N A.
Admitted.

Lemma append_env_weakening (g g': ECCAenv) (N A : ECCAexp):
  ECCA_has_type g N A ->
  ECCA_has_type (appendEnv g g') N A.
Proof.
Admitted.

Lemma append_env_equiv_weakening (g g': ECCAenv) (e e' : ECCAexp):
  ECCA_Equiv g e e' ->
  ECCA_Equiv (appendEnv g g') e e'.
Proof.
Admitted.

Require Import Coq.Program.Equality.

Lemma type_well_typed (g: ECCAenv) (N: ECCAexp) (A: ECCAexp) :
  ECCA_has_type g N A ->
  exists U , ECCA_has_type g A U.
Proof.
  intros. induction H.
  - exists (eUni (uType 1)). apply aT_Ax_Type. auto.
  - exists (eUni (uType (S (S i)))). apply aT_Ax_Type. auto.
  - admit.
  - exists (eUni (uType 1)). apply aT_Ax_Type. auto.
  - exists (eUni (uType 0)). apply aT_Bool. auto.
  - exists (eUni (uType 0)). apply aT_Bool. auto.
  - apply IHECCA_has_type1.
  - exists (eUni (uType 0)). eapply aT_Sig.
Admitted. 

Lemma has_type_wf_g (g: ECCAenv) (N: ECCAexp) (A: ECCAexp) (x : name):
  ECCA_has_type g N A ->
  ECCA_Env_WF g ->
  ECCA_Env_WF (g & x ~ (Def N A)).
Proof.
  intros.  apply type_well_typed in H as H1. destruct H1.
  apply W_Def with (U := x0); auto.
Qed. 
  
Lemma equivalence_in_derivation (g: ECCAenv) (N N' M : ECCAexp) (A B : ECCAexp) (x : name):
ECCA_has_type g N A ->
ECCA_has_type g N' A ->
ECCA_Equiv g N N' ->
ECCA_has_type (ctx_cons g x (Def N A)) M B ->
ECCA_has_type (ctx_cons g x (Def N' A)) M B.
Proof.
  intros. dependent induction H2.
  - apply aT_Ax_Prop. apply has_type_wf_g with (x:=x) in H0. auto.
    inversion H2. auto. 
  - apply aT_Ax_Type. apply has_type_wf_g with (x:=x) in H0. auto.
    inversion H2. auto.
  - shelve.
  - apply aT_Bool. apply has_type_wf_g with (x:=x) in H0. auto.
    inversion H2. auto.
  - apply aT_True. apply has_type_wf_g with (x:=x) in H0. auto.
    inversion H2. auto.
  - apply aT_False. apply has_type_wf_g with (x:=x) in H0. auto.
    inversion H2. auto.
  - apply aT_Sig with (x:=x0). apply IHECCA_has_type1 with (N0:=N); auto.
    shelve.
  - apply aT_Pair. apply IHECCA_has_type1 with (N0:=N); auto.
    apply IHECCA_has_type2 with (N0:=N); auto.
  - apply aT_Prod_Prop with (x:=x0) (i:=i). apply IHECCA_has_type1 with (N0:=N); auto. shelve.
  - apply aT_Prod_Type with (x:=x0). apply IHECCA_has_type1 with (N0:=N); auto. shelve.
  - apply aT_Lam with (x:=x0). shelve.
  - apply aT_Let with (x:=x0) (A:=A0). apply IHECCA_has_type1 with (N0:=N); auto. shelve.
  - eapply aT_If. shelve. apply IHECCA_has_type2 with (N0:=N); auto. shelve.
    shelve.
  - shelve.
  - eapply aT_App. auto. apply IHECCA_has_type1 with (N0:=N); auto.
    apply IHECCA_has_type2 with (N0:=N); auto.
  - eapply aT_Fst. apply IHECCA_has_type with (N0:=N); auto.
  - eapply aT_Snd. apply IHECCA_has_type with (N0:=N); auto.  
Admitted.

  
Lemma Cut_modulo_equivalence (g: ECCAenv) (K : cont) (N N': ECCAexp) (A B: ECCAexp):
(ECCA_cont_has_type g K (Cont N A B) ->
ECCA_has_type g N A ->
ECCA_has_type g N' A ->
ECCA_Equiv g N N' ->
ECCA_has_type g (fill_hole N' K) B)%ECCA.
Proof. 
intros. inversion H ; subst ; cbv.
- assumption. 
- cut (@bind N' 0 (@wk 0 B) = B); simpl_term_eq.
  intros. rewrite <- H3. eapply aT_Let with (n:= N') (m:= M) (A:=A) (B:=(wk B)) (x:=y) (g:=g).
  * assumption.
  * apply equivalence_in_derivation with (N := N); assumption.
Qed. 

Lemma het_compose_equal_fill_hole (K : cont_r) (N: ECCAcomp) :
  (flattenECCAconf (het_compose_r K (Comp N))) = (fill_hole N (@unrestrict_cont 0 K)).
Proof.
  destruct K; simpl; auto.
Qed.  

Lemma appendEnv_rearrange {V:nat}(g g': @ECCAenv V) (x: name) (a: ctxmem) :
  ((appendEnv g g')& x ~ a) = (appendEnv (g & x ~ a) g').
Proof.
  induction g; simpl; auto.
Qed.

Lemma Hetereogeneous_Cut (g g': ECCAenv) (K : cont_r) (M M': ECCAconf) (A B: ECCAexp):
ECCA_cont_has_type (appendEnv g g') (unrestrict_cont K) (Cont M' A B) ->
ECCA_has_type g M A ->
(@ECCA_conf_wf 0 g M) ->
ECCA_Equiv g M M' ->
ECCA_has_type (appendEnv g g') (het_compose_r K M) B.
  intros. induction H1.
  - erewrite het_compose_equal_fill_hole. apply Cut_modulo_equivalence with (A := A) (N:=M').
    assumption. inversion H. assumption. assumption. apply append_env_weakening with (g':=g') in H0.
    assumption. apply aE_Symm. apply append_env_equiv_weakening with (g':=g') in H2. assumption.
  - simpl.
    (* g & x ~ Def n A0 |- m : B -> g |- eLet n m : B *)
    (* ... K is well-typed at g |- (Cont M' A B), g |- B : Type*) inversion H. inversion H0. rewrite <- H8. rewrite <- H13. apply aT_Let with (A:=A2) (x:=x0).
    + apply append_env_weakening with (g':=g') in H12. assumption.
    + erewrite appendEnv_rearrange. admit.
      
Admitted.

 

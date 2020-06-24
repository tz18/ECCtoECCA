Require Export ECCA_typing.
Require Export ECCA_equiv_lemmas.
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

Lemma equivalence_in_derivation (g: ECCAenv) (N N' M : ECCAexp) (A B : ECCAexp) (x : name):
ECCA_has_type g N A ->
ECCA_has_type g N' A ->
ECCA_Equiv g N N' ->
ECCA_has_type (ctx_cons g x (Def N A)) M B ->
ECCA_has_type (ctx_cons g x (Def N' A)) M B.
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

Lemma Hetereogeneous_Cut (g g': ECCAenv) (K : cont_r) (M M': ECCAconf) (A B: ECCAexp):
ECCA_cont_has_type (appendEnv g g') (unrestrict_cont K) (Cont M' A B) ->
ECCA_has_type g M A ->
(@ECCA_conf_wf 0 g M) ->
ECCA_Equiv g M M' ->
ECCA_has_type (appendEnv g g') (het_compose_r K M) B.
Proof.
  intros. induction H1.
  - erewrite het_compose_equal_fill_hole. apply Cut_modulo_equivalence with (A := A) (N:=M'). assumption. inversion H. assumption. assumption. apply append_env_weakening with (g':=g') in H0. assumption. apply equiv_sym. apply append_env_equiv_weakening with (g':=g') in H2. assumption.
  - simpl. Admitted.

    
 

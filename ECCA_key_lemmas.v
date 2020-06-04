Require Export ECCA_typing.
Require Export ECCA_equiv_lemmas.
Require Export ECCA_continuations.

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

Lemma weakening (g : ECCAenv) (x : name) (N A A' U : ECCAexp):
  ECCA_has_type g N A ->
  ECCA_has_type (ctx_cons g x (Assum A')) N A.
Proof.
Admitted.

Lemma def_weakening (g : ECCAenv) (x : name) (N N' A A' : ECCAexp):
  ECCA_has_type g N A ->
  ECCA_has_type (ctx_cons g x (Def N' A')) N A.
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

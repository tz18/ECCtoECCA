Require Export typing.
Require Export equiv_lemmas.
Require Export continuations.
Require Export ECCA_het_comp.

Lemma Cut (g: env) (K : cont) (N: exp) (A B: exp):
(Types_cont g K (Cont N A B) ->
Types g N A ->
Types g (fill_hole N K) B)%ECCA.
Proof. 
intros. inversion H ; subst ; cbv.
- assumption. 
- cut (@bind N 0 (@wk 0 B) = B); simpl_term_eq. 
  intros. rewrite <- H1. eapply aT_Let with (n:= N) (m:= M) (A:=A) (B:=(wk B)) (x:=y) (g:=g); assumption.
Qed.

Lemma weakening (g : env) (x : name) (N A A' : exp):
  Types g N A ->
  Types (ctx_cons g x (Assum A')) N A.
Proof.
Admitted.

Lemma def_weakening (g : env) (x : name) (N N' A A' : exp):
  Types g N A ->
  Types (ctx_cons g x (Def N' A')) N A.
Admitted.

Lemma append_env_weakening (g g': env) (N A : exp):
  Types g N A ->
  Types (append g g') N A.
Proof.
Admitted.

Lemma append_env_equiv_weakening (g g': env) (e e' : exp):
  Equiv g e e' ->
  Equiv (append g g') e e'.
Proof.
Admitted.

Lemma equivalence_in_derivation (g: env) (N N' M : exp) (A B : exp) (x : name):
Types g N A ->
Types g N' A ->
Equiv g N N' ->
Types (ctx_cons g x (Def N A)) M B ->
Types (ctx_cons g x (Def N' A)) M B.
Admitted.

  
Lemma Cut_modulo_equivalence (g: env) (K : cont) (N N': exp) (A B: exp):
(Types_cont g K (Cont N A B) ->
Types g N A ->
Types g N' A ->
Equiv g N N' ->
Types g (fill_hole N' K) B)%ECCA.
Proof. 
intros. inversion H ; subst ; cbv.
- assumption. 
- cut (@bind N' 0 (@wk 0 B) = B); simpl_term_eq.
  intros. rewrite <- H3. eapply aT_Let with (n:= N') (m:= M) (A:=A) (B:=(wk B)) (x:=y) (g:=g).
  * assumption.
  * apply equivalence_in_derivation with (N := N); assumption.
Qed. 

Lemma het_compose_equal_fill_hole (K : cont_r) (N: comp) :
  (flattenconf (het_compose_r K (Comp N))) = (fill_hole N (@unrestrict_cont 0 K)).
Proof.
  destruct K; simpl; auto.
Qed.  

Lemma append_rearrange {V:nat}(g g': @env V) (x: name) (a: ctxmem) :
  ((append g g')& x ~ a) = (append (g & x ~ a) g').
Proof.
  induction g; simpl; auto.
Qed.

Lemma Hetereogeneous_Cut (g g': env) (K : cont_r) (M M': conf) (A B: exp):
Types_cont (append g g') (unrestrict_cont K) (Cont M' A B) ->
Types g M A ->
(@WellBound_conf 0 g M) ->
Equiv g M M' ->
Types (append g g') (het_compose_r K M) B.
Proof.
  intros. induction H1.
  - erewrite het_compose_equal_fill_hole. apply Cut_modulo_equivalence with (A := A) (N:=M').
    assumption. inversion H. assumption. assumption. apply append_env_weakening with (g':=g') in H0.
    assumption. apply equiv_sym. apply append_env_equiv_weakening with (g':=g') in H2. assumption.
  - simpl. inversion H. inversion H0. rewrite <- H8. rewrite <- H13. apply aT_Let with (A:=A2) (x:=x0).
    + apply append_env_weakening with (g':=g') in H12. assumption.
    + erewrite append_rearrange. admit.
      
Admitted.

 

Require Export typing.
Require Export equiv_lemmas.
Require Export continuations.

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

Require Import Coq.Program.Equality.

Lemma type_well_typed (g: env) (N: exp) (A: exp) :
  Types g N A ->
  exists U , Types g A U.
Proof.
  intros. induction H.
  - exists (eUni (uType 1)). apply aT_Ax_Type. auto.
  - exists (eUni (uType (S (S i)))). apply aT_Ax_Type. auto.
  - admit.
  - exists (eUni (uType 1)). apply aT_Ax_Type. auto.
  - exists (eUni (uType 0)). apply aT_Bool. auto.
  - exists (eUni (uType 0)). apply aT_Bool. auto.
  - apply IHTypes1.
  - exists (eUni (uType 0)). eapply aT_Sig.
Admitted. 

Lemma has_type_wf_g (g: env) (N: exp) (A: exp) (x : name):
  Types g N A ->
  WellFormed g ->
  WellFormed (g & x ~ (Def N A)).
Proof.
  intros.  apply type_well_typed in H as H1. destruct H1.
  apply W_Def with (U := x0); auto.
Qed. 
  
Lemma equivalence_in_derivation (g: env) (N N' M : exp) (A B : exp) (x : name):
Types g N A ->
Types g N' A ->
Equiv g N N' ->
Types (ctx_cons g x (Def N A)) M B ->
Types (ctx_cons g x (Def N' A)) M B.
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
  - apply aT_Sig with (x:=x0). apply IHTypes1 with (N0:=N); auto.
    shelve.
  - apply aT_Pair. apply IHTypes1 with (N0:=N); auto.
    apply IHTypes2 with (N0:=N); auto.
  - apply aT_Prod_Prop with (x:=x0) (i:=i). apply IHTypes1 with (N0:=N); auto. shelve.
  - apply aT_Prod_Type with (x:=x0). apply IHTypes1 with (N0:=N); auto. shelve.
  - apply aT_Lam with (x:=x0). shelve.
  - apply aT_Let with (x:=x0) (A:=A0). apply IHTypes1 with (N0:=N); auto. shelve.
  - eapply aT_If. shelve. apply IHTypes2 with (N0:=N); auto. shelve.
    shelve.
  - shelve.
  - eapply aT_App. auto. apply IHTypes1 with (N0:=N); auto.
    apply IHTypes2 with (N0:=N); auto.
  - eapply aT_Fst. apply IHTypes with (N0:=N); auto.
  - eapply aT_Snd. apply IHTypes with (N0:=N); auto.  
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
  (unrestrict_conf (het_compose_r K (Comp N))) = (@unrestrict_conf 0 (fill_hole_r N K)).
Proof.
  destruct K; simpl; auto.
Qed.  

Lemma append_rearrange {V:nat}(g g': @env V) (x: name) (a: ctxmem) :
  ((append g g')& x ~ a) = (append (g & x ~ a) g').
Proof.
  induction g; simpl; auto.
Qed.

Lemma Hetereogeneous_Cut (g g': env) (K : cont_r) (M M': conf) (A B: exp):
Types_cont (append g g') (unrestrict_cont K) (Cont (unrestrict_conf M') A B) ->
Types g (unrestrict_conf M) A ->
(@WellBound_conf 0 g M) ->
Equiv g (unrestrict_conf M) (unrestrict_conf M') ->
Types (append g g') (unrestrict_conf (het_compose_r K M)) B.
  intros. induction H1.
  - erewrite het_compose_equal_fill_hole. apply Cut_modulo_equivalence with (A := A) (N:=(unrestrict_conf M')).
    assumption. inversion H. assumption. assumption. apply append_env_weakening with (g':=g') in H0.
    assumption. apply aE_Symm. apply append_env_equiv_weakening with (g':=g') in H2. assumption.
  - simpl.
    (* g & x ~ Def n A0 |- m : B -> g |- eLet n m : B *)
    (* ... K is well-typed at g |- (Cont M' A B), g |- B : Type*) inversion H. inversion H0. rewrite <- H8. rewrite <- H13. apply aT_Let with (A:=A2) (x:=x0).
    + apply append_env_weakening with (g':=g') in H12. assumption.
    + erewrite append_rearrange. admit.
      
Admitted.

 

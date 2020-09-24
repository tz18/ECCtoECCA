Require Export typing.
Require Export equiv.
Require Export continuations.
Require Export continuations_lemmas.

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
  (unrestrict_conf (het_compose_r K (Comp N))) = (fill_hole N (@unrestrict_cont 0 K)).
Proof.
  destruct K; simpl; auto.
Qed.  

Lemma append_rearrange {V:nat}(g g': @env V) (x: name) (a: ctxmem) :
  ((append g g')& x ~ a) = (append (g & x ~ a) g').
Proof.
  induction g; auto.
Qed.

Lemma cont_return_type_well_typed (g : env) (K : cont_r) (M : conf) (A B: exp):
  Types_cont g (unrestrict_cont K) (Cont M A B) ->
  exists U , Types g B U.
Proof.
  intros. dependent induction H.
  + apply type_well_typed in H. auto. 
  + apply type_well_typed in H0.
    (* need B : U but have (open y (wk B)) : U *)
    shelve.
Admitted.

Lemma shift_no_free (g : env) (B: exp) (x: name):
  (exists U, Types g B U) ->
  B = (open x (wk B)).
Admitted.

Lemma aT_Let_no_bind (g : env) (M : @exp 1) (N A B: exp) (x: name):
  Types g N A ->
  Types (g & x ~ Def N A) (open x M) B ->
  (exists U, Types g B U) ->
  Types g (eLet N M) B.
Proof.
  intros. cut ((bind N (wk B)) = B).
  - intros. rewrite <- H2. apply aT_Let with (A:=A) (x:=x).
    * apply H.
    * apply shift_no_free with (x:=x) in H1.
      rewrite <- H1. auto.
  - simpl_term_eq.
Qed. 

Lemma aT_If_no_bind (g : env) (V B M1 M2: exp) (x y: name):
  Types g V eBool ->
  Types (g & y ~ (Eq V eTru)) M1 B ->
  Types (g & y ~ (Eq V eFls)) M2 B ->
  (exists U, Types (g & x ~ Assum eBool) B U) ->
  Types g (eIf V M1 M2) B.
Proof.
  intros. cut ((bind V (wk B)) = B).
  - intros. rewrite <- H3. assert (H4:=H2). destruct H2. apply aT_If with (x:=x) (y:=y) (U:=x0).
    * apply shift_no_free with (x:=x) in H4 as H5.
      rewrite H5 in H2. auto.
    * auto.
    * cut ((bind eTru (wk B)) = B). intros. 
      rewrite H5. auto. simpl_term_eq.
    * cut ((bind eFls (wk B)) = B). intros. 
      rewrite H5. auto. simpl_term_eq.
  - simpl_term_eq.
Qed. 

Lemma open_wk_het_comp (K : cont_r) (M : conf) (x: name):
  open x (het_compose_r (wk_cont K) M) = (het_compose_r K (@open_conf 0 x M)).
Admitted.

Lemma defn_well_typed (g: env) (N M B: exp) :
  Types g (eLet N M) B ->
  exists A, Types g N A.
Proof.
  intros. dependent induction H.
  - exists A. auto.
  - apply IHTypes1 with (M0:=M). auto.
Qed. 
  
                

Set Printing Implicit.

Lemma Hetereogeneous_Cut (g g': env) (K : cont_r) (M M': conf) (A B: exp):
Types_cont (append g g') (unrestrict_cont K) (Cont M' A B) ->
Types g M A ->
(@WellBound_conf 0 g M) ->
Equiv g M M' ->
Types (append g g') (het_compose_r K M) B.
  intros. induction H1.
  - erewrite het_compose_equal_fill_hole. apply Cut_modulo_equivalence with (A := A) (N:=M').
    assumption. inversion H. assumption. assumption. apply append_env_weakening with (g':=g') in H0.
    assumption. apply aE_Symm. apply append_env_equiv_weakening with (g':=g') in H2. assumption.
  - simpl. pose (defn_well_typed g n m A H0)as H3. destruct H3.
    eapply aT_Let_no_bind.
    * apply append_env_weakening with (g':=g') in H3. apply H3.
    * pose (append_rearrange g g' x (Def n A)) as H4.
      pose (open_wk_het_comp K m x) as H5. rewrite H5. shelve.
    * apply cont_return_type_well_typed in H. auto.
  - simpl. apply aT_If_no_bind with (x:=x) (y:=y).
    * shelve.
    * pose (append_rearrange g g' y (Eq (unrestrict_val v) eTru)) as H3.
      shelve. (*??? what the heLL*)
    * shelve.
    * apply cont_return_type_well_typed in H.
      destruct H. apply weakening with (x:=x) (A':=eBool) in H.
      exists x0. auto.
      
Admitted.

 

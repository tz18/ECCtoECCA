Require Export typing.
Require Export equiv.
Require Export continuations.
Require Export continuations_lemmas.
Require Export typing_lemmas.

Lemma Cut (g: env) (K : cont) (N: exp) (A B: exp):
(Types_cont g K (Cont N A B) ->
Types g N A ->
Types g (fill_hole N K) B)%ECCA.
Proof. 
intros. inversion H ; subst ; cbv.
- assumption. 
- cut (@bind N 0 (@wk 0 B) = B); simpl_term_eq. 
  intros. rewrite <- H1. apply Type_well_typed in H5. destruct H5. eapply aT_Let with (n:= N) (m:= M) (A:=A) (B:=(wk B)) (x:=y) (g:=g).
  eauto. apply H0. auto.
Qed.

Lemma eq_in_dev_1 g N N' A:
(g ⊢ N : A) ->
(g ⊢ N' : A) ->
(g ⊢ N ≡ N') ->
forall x x0 A0,
assumes (g & x ~ Def N A) x0 A0 ->
assumes (g & x ~ Def N' A) x0 A0.
Proof.
intros. inversion H2. 
apply has_inversion in H3. apply get_inversion in H3.
destruct H3 as [n [H4 [[g' [A' [H5]]] | [g' [y [A' [x' [B [H3 [H5 [H6]]]]]]]]]]].
+ subst. inversion H5. subst. auto with contexts.
+ subst. inversion H3. subst. destruct B. names in H7. inversion H7. subst.
Admitted. 
(* 

Lemma equivalence_in_context_has_equivalent_def:
forall g e A,
Types g e A ->
forall x x0 e1 A1,
g & x ~ Def e A ∋ x0 ~ Def e1 A1 ->
forall e',
Types g e' A ->
Equiv g e e' ->
exists e2, Equiv g e1 e2 /\
g & x ~ Def e' A ∋ x0 ~ Def e2 A1.
Proof.
intros. apply has_inversion in H0. apply get_inversion in H0.
destruct H0 as [n [H4 [[g' [A' [H5]]] | [g' [y [A' [x' [B [H3 [H5 [H6]]]]]]]]]]].
+ subst. inversion H5. subst. names in H0. inversion H0. subst. exists ([^n] e').
  split. .
(* *)*)



Lemma equivalence_in_derivation_steps:
forall (e : exp) (g : env) (N A : exp),
(g ⊢ N : A) ->
forall (x : name) (e' : exp),
(g & x ~ Def N A ⊢ e ⊳ e') ->
forall N' : exp,
(g ⊢ N' : A) ->
(g ⊢ N ≡ N') ->
exists e'' : exp,
  (g & x ~ Def N' A ⊢ e' ≡ e'') /\
  (g & x ~ Def N' A ⊢ e ⊳ e'').
Proof.
intros. remember (g & x ~ Def N A) as g0. induction H0.
+ subst. esplit. Admitted.



(* Lemma equivalence_in_derivation_reduces:
forall e g N A,
Types g N A ->
forall x e',
Reduces (ctx_cons g x (Def N A)) e e' ->
forall N',
Types g N' A ->
Equiv g N N' ->
Reduces (ctx_cons g x (Def N' A)) e e'.
Proof.
intros. remember (g & x ~ Def N A0) as g0. induction H0.
+ subst. apply aE_Step with (e:=e). *)

Lemma equivalence_in_derivation_equiv:
forall (M : exp) (g : env) (N A : exp),
(g ⊢ N : A) ->
forall (x : name) (B : exp),
(g & x ~ Def N A ⊢ M ≡ B) ->
forall N' : exp,
(g ⊢ N' : A) ->
(g ⊢ N ≡ N') ->
(g & x ~ Def N' A ⊢ M ≡ B).
Proof.
intros. remember (g & x ~ Def N A) as g0. induction H0.
+ subst. apply equivalence_in_derivation_steps with (N':=N') in H0.
  destruct H0. destruct H0. apply aE_Trans with (M':=x0).
  - apply aE_Step with (e:=e). apply H3.
  - auto.
  - auto.
  - auto.
  - auto.
Admitted.
 
Lemma equivalence_in_derivation_subtypes:
forall M g N A,
Types g N A ->
forall x B,
SubTypes (ctx_cons g x (Def N A)) M B ->
forall N',
Types g N' A ->
Equiv g N N' ->
SubTypes (ctx_cons g x (Def N' A)) M B.
Proof. intros. remember (g & x ~ Def N A) as g0. induction H0.
+ subst. apply ST_Cong.
Admitted.


Lemma equivalence_in_derivation :
forall M g N A,
Types g N A ->
forall x B,
Types (ctx_cons g x (Def N A)) M B ->
forall N',
Types g N' A ->
Equiv g N N' ->
Types (ctx_cons g x (Def N' A)) M B.
Proof. intros. remember (g & x ~ Def N A) as g0. induction H0; eauto; intros.
  + apply aT_Ax_Prop. apply has_type_wf_g. auto. apply Types_only_if_wellformed with N A; auto.
  + apply aT_Ax_Type. apply has_type_wf_g. auto. apply Types_only_if_wellformed with N A; auto.
  + apply aT_Var. subst. inversion H0. subst. apply wf_Def with U; eauto. subst.
    apply eq_in_dev_1 with N; eauto.
  + apply aT_Bool. rewrite Heqg0 in H0. inversion H0. subst. apply wf_Def with U; eauto.
  + apply aT_True. apply has_type_wf_g with (x:=x) in H; eauto.
    inversion H; eauto.
  + apply aT_False. apply has_type_wf_g with (x:=x) in H; eauto.
    inversion H; eauto.
  + apply aT_Sig with (x:=x0). apply IHTypes1; auto. subst. (* apply IHTypes2. rewrite Heqg0 in H2_. *)
    shelve.
  + shelve.
  + shelve.
  + shelve.
  + shelve.
  + shelve.
  + subst. apply aT_Conv with (A:=A0) (U:=U). eauto. eauto. Admitted.

(*   - apply aT_Pair. apply IHTypes1 with (N0:=N); auto.
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
Admitted. *)

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
  intros. rewrite <- H3. 
  apply Type_well_typed in H0 as H10. destruct H10 as [U].
  apply aT_Let with (n:= N') (m:= M) (A:=A) (B:=(wk B)) (x:=y) (g:=g) (U:=U).
  *  eauto.
  * assumption.
  * apply equivalence_in_derivation with (N := N); assumption.
Qed.

Lemma append_rearrange {V:nat}(g g': env) (x: name) (a: ctxmem) :
  ((append g g')& x ~ a) = (append (g & x ~ a) g').
Proof.
  induction g; auto.
Qed.



Lemma cont_return_type_well_typed (g : env) (K : cont) (iK: cont_is_ANF K) (M : exp) (iM: isConf M) (A B: exp):
  Types_cont g K (Cont M A B) ->
  exists U , Types g B U.
Proof.
  intros. dependent induction H.
  + apply type_well_typed in H. auto. eapply type_requires_well_formed. apply H.
  + apply type_well_typed in H0. names in H0.
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

Lemma Hetereogeneous_Cut (g g': env) (K : cont) (pK: cont_is_ANF K) (M M': exp) (pM: isConf M) (pM': isConf M') (A A' B: exp):
Types_cont (append g g') K (Cont M' A' B) ->
Types g M A ->
Types g M' A' ->
Equiv (append g g') M M' ->
Equiv (append g g') A A' ->
Types (append g g') (het_compose K M) B.
Proof.
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
      
Admitted. *)
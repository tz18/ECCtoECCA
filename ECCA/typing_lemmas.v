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

(* vvv Not true vvv*)
(* Definition WellFormed_weakening Γ (pWF: (⊢ Γ)):=
  forall r Δ,
    Γ =[r]=> Δ ->
    (⊢ Δ). *)

Lemma Types_only_if_wellformed Γ e A:
(Γ ⊢ e : A)->
(⊢ Γ). 
Proof.
intros.
induction H; auto.
Qed.
Hint Resolve Types_only_if_wellformed.

Lemma Type_weakening Γ e A (pT: (Γ ⊢ e : A)):
  forall r Δ,
    Γ =[r]=> Δ ->
    (⊢ Δ) ->
    (Δ ⊢ ([r] e) : [r] A).
Proof. 
induction pT; auto.
all: try (intros; constructor; eauto; fail).
+ intros. names. destruct H1 eqn:H3. 
  rewrite applyt_is_applyv with (rn:=total). names. apply aT_Var.
   - eauto.
   - unfold assumes. destruct H0. 
      * apply f in H0. left. names in H0. apply H0.
      * destruct H0. apply f in H0. right. eauto. 
+ intros. names. apply aT_Sig with (x:=x). eauto.
  names. apply IHpT2 with (Δ:= (Δ & x ~ Assum ([r] A))) (r:= (r,, x)%ren).
  apply ctx_rename; eauto. apply wf_Assum with (uType i); eauto.
+  intros. names. apply aT_Pair.
  - auto.
  - specialize IHpT2 with (r:=r) (Δ:=Δ). names in IHpT2. apply IHpT2; eauto.
(*   - specialize IHpT3 with (r:=r) (Δ:=Δ). names in IHpT3. apply IHpT3; eauto. *)
+  intros. names. eapply aT_Prod_Prop with (x:=x). eauto.
  names. apply IHpT2 with (Δ:= (Δ & x ~ Assum ([r] A))) (r:= (r,, x)%ren).
  apply ctx_rename. auto. eauto.
+  intros. names. eapply aT_Prod_Type with (x:=x). eauto.
  names. apply IHpT2 with (Δ:= (Δ & x ~ Assum ([r] A))) (r:= (r,, x)%ren).
  apply ctx_rename. auto. eauto.
+  intros. names. eapply aT_Lam with (x:=x). eauto.
  names. apply IHpT2 with (Δ:= (Δ & x ~ Assum ([r] A))) (r:= (r,, x)%ren).
  apply ctx_rename. auto. apply wf_Assum with (uType i); eauto.
+  intros. names. apply aT_Let with (x:=x) (A:=([r]A)) (U:=U); eauto.
  names. apply IHpT3 with (Δ:= (Δ & x ~ Def ([r] n) ([r] A))) (r:= (r,, x)%ren).
  apply ctx_rename. auto. apply wf_Def with U; eauto.
+  intros. names. apply aT_If with (x:=x) (p:=p) (U:=U). 
  - names. apply IHpT1 with (Δ:= (Δ & x ~ Assum eBool)) (r:= (r,, x)%ren).
    apply ctx_rename. auto. eauto.
  - eauto.
  - names. specialize IHpT3 with (Δ:= (Δ & p ~ Assum (eEqv ([r] e) eTru))) (r:= (r,, p)%ren). names in IHpT3. apply IHpT3.
    apply ctx_rename. auto. eapply wf_Assum with (uType 0). auto.
    apply aT_Equiv with (B:= eBool); eauto.
  - names. specialize IHpT4 with (Δ:= (Δ & p ~ Assum (eEqv ([r] e) eFls))) (r:= (r,, p)%ren). names in IHpT4. apply IHpT4.
    apply ctx_rename. auto. eapply wf_Assum with (uType 0). auto.
    apply aT_Equiv with (B:= eBool); eauto.
+ intros. apply aT_Conv with (A:=[r]A)(U:=U); eauto.
  apply SubTypes_weakening with g; auto.
+  intros. names. apply aT_App with ([r]A').
  - apply IHpT1; auto.
  - apply IHpT2; auto.
+ intros. names. apply aT_Fst with ([r]B). apply IHpT; auto.
+ intros. names. apply aT_Snd with ([r]A). apply IHpT; auto.
+ intros. names. apply aT_Refl with ([r]A). auto.
+ intros. names. apply aT_Equiv with (B:=[r]B); eauto.
Qed.

(* Theorem weakening {Γ e A pT pWF}:
Type_weakening Γ e A pT /\ WellFormed_weakening Γ pWF.
Proof.
induction Types_WellFormed_mutind with (P:=Type_weakening) (P0:=WellFormed_weakening). auto.
all: try (intros; constructor; eauto; fail); unfold Type_weakening. *)

Lemma cons_weakening_assum (g: env) (A A': exp) (x: name):
(g ⊢ A : A') ->
  (forall B (U: universe), 
   ((g ⊢ B : eUni U) -> 
   (g & x ~ Assum B ⊢ [^x] A : [^x] A'))).
Proof.
intros. apply Type_weakening with g; auto. apply ctx_shift; apply ctx_id.
apply wf_Assum with U; auto. apply Types_only_if_wellformed with A A'; auto. 
Qed.

Lemma cons_weakening_def (g: env) (A A': exp) (x: name):
(g ⊢ A : A') ->
  (forall B U e, 
   ((g ⊢ B : eUni U) ->
    (g ⊢ e : B) ->
   (g & x ~ Def e B ⊢ [^x] A : [^x] A'))).
Proof.
intros. apply Type_weakening with g; auto. apply ctx_shift; apply ctx_id.
apply wf_Def with U; auto. apply Types_only_if_wellformed with A A'; auto.
Qed.

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

(* Lemma typing_is_broken_part_1: 
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
Qed. *)

(* Lemma typing_is_broken_part_2: 
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
Qed. *)
(* Conclusion: We need to shift the bodies of ass/defs in the context when we add a new ass/def *)

Lemma shift_uni_id:
forall x U {V},
([^x] (@eUni V U)) = (@eUni V U).
Proof. auto. Qed.

Lemma WellFormed_implies_well_typed_assum (g: env):
WellFormed g ->
forall (v: var) (A: exp),
(has g v (Assum A)) ->
exists U, Types g A (eUni U).
Proof.
induction 1.
+ intros. inversion H.
+ intros. rename H0 into H2. rename H1 into H0. rename H2 into H1. 
  apply has_inversion in H0. apply get_inversion in H0.
  destruct H0. destruct H0. inversion H0. subst.
  destruct H2.
  * destruct H0 as [g']. destruct H0 as [c]. destruct H0.
    inversion H0. subst. names in H2. inversion H2. subst. destruct H0.
    exists U. rewrite <- shift_uni_id with (x:=x0). apply cons_weakening_assum with U; auto.
  * destruct H0 as [g']. destruct H0. destruct H0 as [c]. destruct H0. destruct H0 as [c'].
    destruct H0. destruct H2. destruct H3. inversion H0. subst. clear H0.
    destruct H4. cut (has g' x2 c'). intro. cut (exists B, c' = Assum B). intro. 
    destruct H5 as [B]. subst. names in H3. inversion H3. subst.
    apply IHWellFormed in H4. destruct H4 as [B'].
    apply cons_weakening_assum with (A:=B) (A':=eUni B')(x:=x1) in H1.
    eauto. eauto. unfold apply in H3. destruct c'. eauto. discriminate.
    unfold has. rewrite H0. auto.
+ intros. apply has_inversion in H2. apply get_inversion in H2.
  destruct H2. destruct H2. destruct H3.
  * destruct H3. destruct H3. destruct H3.
    inversion H3. subst. inversion H4.
  * destruct H3 as [g']. destruct H3. destruct H3 as [c]. destruct H3.
    destruct H3 as [c']. destruct H3. destruct H4. destruct H5.
    inversion H3. subst. clear H3.
    cut (has g' x2 c'). cut (exists B, c' = Assum B). intros.
    destruct H2 as [B]. subst. names in H6. inversion H6. subst.
    apply IHWellFormed in H3. destruct H3 as [B'].
    apply cons_weakening_def with (A:=B) (A':=eUni B') (U:=U)(x:=x1) in H1.
    all: eauto. unfold apply in H6. destruct c'. eauto. discriminate. unfold has. rewrite H5. auto.
Qed.

Lemma WellFormed_implies_well_typed_def (g: env):
WellFormed g ->
forall (v: var) (A: exp) (e: exp),
(has g v (Def e A)) ->
exists U, Types g A (eUni U).
Proof.
induction 1.
+ intros. inversion H.
+ intros. rename H0 into H2. rename H1 into H0. rename H2 into H1. 
  apply has_inversion in H0. apply get_inversion in H0.
  destruct H0. destruct H0. inversion H0. subst.
  destruct H2.
  * destruct H0. destruct H0. destruct H0. inversion H0. subst. inversion H2. 
  * destruct H0 as [g']. destruct H0. destruct H0 as [c]. destruct H0. destruct H0 as [c'].
    destruct H0. destruct H2. destruct H3. inversion H0. subst. clear H0.
    destruct H4. cut (has g' x2 c'). intro. cut (exists e' B, c' = Def e' B). intro. 
    destruct H5 as [e']. destruct H5 as [B]. subst. names in H3. inversion H3. subst.
    apply IHWellFormed in H4. destruct H4 as [B'].
    apply cons_weakening_assum with (A:=B) (A':=eUni B')(x:=x1) in H1.
    eauto. eauto. unfold apply in H3. destruct c'. discriminate. eauto.
    unfold has. rewrite H0. auto.
+ intros. apply has_inversion in H2. apply get_inversion in H2.
  destruct H2. destruct H2. destruct H3.
  * destruct H3 as [g']. destruct H3 as [c]. destruct H3.
    inversion H3. subst. names in H4. inversion H4. subst. destruct H4.
    exists U. rewrite <- shift_uni_id with (x:=x0). apply cons_weakening_def with U; auto.
  * destruct H3 as [g']. destruct H3. destruct H3 as [c]. destruct H3. destruct H3 as [c'].
    destruct H3. destruct H4. destruct H5. inversion H3. subst. clear H3.
    cut (has g' x2 c'). intro. cut (exists e' B, c' = Def e' B). intro. 
    destruct H3 as [e']. destruct H3 as [B]. subst. names in H6. inversion H6. subst.
    apply IHWellFormed in H2. destruct H2 as [B']. exists (B').
    apply cons_weakening_def with (A:=B) (A':=eUni B')(x:=x1) (U:=U); eauto.
    unfold apply in H6. destruct c'. discriminate. eauto.
    unfold has. rewrite H5. auto.
Qed.

Lemma universe_lt_st:
forall g,
(⊢ g) ->
forall i i',
(lt i i') ->
(g ⊢ (eUni (uType i)) ≲ (eUni (uType i'))).
Proof. 
intros. induction H0. apply ST_Cum.
eapply ST_Trans. apply IHle. apply ST_Cum.
Qed.

Lemma universe_lt:
forall g,
(⊢ g) ->
forall i i',
(lt i i') ->
(g ⊢ (eUni (uType i)) : (eUni (uType i'))).
Proof. 
intros. induction H0.
  - eauto.
  - eapply aT_Conv. apply IHle. auto. auto.
Qed.  

Import Coq.Arith.Compare_dec.
Import Lia.

Lemma unis_dont_step:
forall g U U',
(g ⊢ eUni U ⊳ eUni U') -> U = U'.
Proof.
inversion 1. Qed.

Lemma unis_dont_reduce:
forall g U e,
(g ⊢ eUni U ⊳* e) -> e = eUni U.
Proof.
intros. remember (eUni U) as e1 in H. 
induction H; try discriminate.
+ subst. inversion H.
+ subst. auto.
+ subst. destruct IHReduces1. auto. apply IHReduces2. auto. 
Qed.

Lemma type_not_subtype_prop:
forall g,
(⊢ g) ->
forall i,
(g ⊢ eUni (uType i) ≲ eUni uProp) -> False.
Proof.
intros.
inversion H0.
+ subst. inversion H1. subst. 
- apply unis_dont_step in H2. discriminate.
- subst. (* H2 : assumes g x (eEqv (eUni (uType i)) (eUni uProp))*) 
(* there is actually nothing to prevent us from assuming things that aren't true *)
Abort.

Lemma universe_type_if:
forall g,
forall U e,
(g ⊢ eUni U : e) ->
(g ⊢ eUni U ≲ e).
Proof. intros. remember (eUni U) as e1 in H. 
induction H; try discriminate.
  - inversion Heqe1. eauto.
  - inversion Heqe1. eauto.
  - subst. apply ST_Trans with (A':=A). apply IHTypes1. auto. auto.
Qed.

Lemma universe_type_common_parent:
forall g,
(⊢ g) ->
forall i i', 
exists i'', 
(g ⊢ (eUni (uType i)) : (eUni (uType i''))) /\
(g ⊢ (eUni (uType i')) : (eUni (uType i''))).
Proof.
intros. destruct (Nat.compare i i') eqn:Heq.
+ apply nat_compare_eq in Heq. rewrite Heq. exists (S (i')). eauto.
+ apply nat_compare_lt in Heq. exists (S i'). split.
  apply universe_lt; eauto. eauto.
+ apply nat_compare_gt in Heq. exists (S i). split.
  - apply universe_lt; eauto.
  - cut (i' < i). intro. apply universe_lt; eauto. auto.
Qed.

Lemma universe_type_common_subtype:
forall g,
(⊢ g) ->
forall i i', 
exists i'', 
(g ⊢ (eUni (uType i)) ≲ (eUni (uType i''))) /\
(g ⊢ (eUni (uType i')) ≲ (eUni (uType i''))).
Proof.
intros. destruct (Nat.compare i i') eqn:Heq.
+ apply nat_compare_eq in Heq. rewrite Heq. exists (S (i')). eauto.
+ apply nat_compare_lt in Heq. exists (S i'). split.
  apply universe_lt_st; eauto. eauto.
+ apply nat_compare_gt in Heq. exists (S i). split.
  - apply universe_lt_st; eauto.
  - cut (i' < i). intro. apply universe_lt_st; eauto. auto.
Qed.

Lemma universe_common_parent:
forall g,
(⊢ g) ->
forall U U', 
exists U'', 
(g ⊢ (eUni U) : (eUni U'')) /\
(g ⊢ (eUni U') : (eUni U'')).
Proof.
intros. destruct U; destruct U'.
+ exists (uType 0). auto.
+ exists (uType (S i)). split. 
  - eapply aT_Conv. apply aT_Ax_Prop. auto. auto. apply universe_lt_st. auto. lia.
  - apply universe_lt; auto.
+ exists (uType (S i)). split. 
  - apply universe_lt; auto.
  - eapply aT_Conv. apply aT_Ax_Prop. auto. auto. apply universe_lt_st. auto. lia.
+ cut (exists i'', (g ⊢ eUni (uType i) : eUni (uType i'')) /\
  (g ⊢ eUni (uType i0) : eUni (uType i''))). intro. destruct H0. exists (uType x). auto.
  apply universe_type_common_parent. auto.
Qed.

Lemma universe_common_parent_type:
forall g,
(⊢ g) ->
forall U U', 
exists i, 
(g ⊢ (eUni U) : (eUni (uType i))) /\
(g ⊢ (eUni U') : (eUni (uType i))).
Proof.
intros. destruct U; destruct U'.
+ eauto.
+ exists ((S i)). split. 
  - eapply aT_Conv. apply aT_Ax_Prop. auto. auto. apply universe_lt_st. auto. lia.
  - apply universe_lt; auto.
+ exists ((S i)). split. 
  - apply universe_lt; auto.
  - eapply aT_Conv. apply aT_Ax_Prop. auto. auto. apply universe_lt_st. auto. lia.
+ cut (exists i'', (g ⊢ eUni (uType i) : eUni (uType i'')) /\
  (g ⊢ eUni (uType i0) : eUni (uType i''))). intro. destruct H0. exists (x). auto.
  apply universe_type_common_parent. auto.
Qed.

Lemma universe_common_parent_subtype:
forall g,
(⊢ g) ->
forall U U', 
exists i, 
(g ⊢ (eUni U) ≲ (eUni (uType i))) /\
(g ⊢ (eUni U') ≲ (eUni (uType i))).
Proof.
intros. destruct U; destruct U'.
+ eauto.
+ exists ((S i)). split. 
  - eapply ST_Trans. eapply ST_Prop. eapply universe_lt_st; auto. lia.
  - apply universe_lt_st; auto.
+ exists ((S i)). split. 
  - apply universe_lt_st; auto.
  - eapply ST_Trans. eapply ST_Prop. eapply universe_lt_st; auto. lia.
+ cut (exists i'', (g ⊢ eUni (uType i) : eUni (uType i'')) /\
  (g ⊢ eUni (uType i0) : eUni (uType i''))). intro. destruct H0. 
  apply universe_type_common_subtype. auto. apply universe_type_common_parent. auto.
Qed.

Compute (close "x" (eId (free "x"))).
Compute (eId (@bound 1 l0)).

(*Lemma bind_inversion (a: @exp 0) (v: @exp 0) (b: @exp 1):
bind v b = a ->
wk a = b \/ 
((b = (eId (@bound (1) l0))) /\ a = v)
\/
(exists l: level, (b = (eId (bound (S l)))) /\ a = (eId (bound l))).

Proof. intros. destruct b.
+ destruct x.
  - names in H. left. cut (@eId 1 (@free 1 name) = wk (@eId 0 (@free 0 name))).
    * intro. rewrite H0. apply f_equal. auto.
    * names. auto.
  - destruct l.
    * right. auto.
    * left. names in H. subst. auto. 
+ names in H. left. subst. auto.
+ names in H. left. subst. auto.  *)

(* Lemma substitution_definition:
forall g v A B U, 
(g ⊢ bind v B : eUni U) ->
(g ⊢ v : A) ->
forall g' r,
relates g r g' ->
forall x,
has g' (free x) (Def v A) ->
(g' ⊢ open x ([r] B): eUni U).
Proof. intros. induction H.
+ subst.
 *)

(* I need an induction principle for V=1, not just V=0 *)
Lemma substitution_definition:
forall g v A B U U', 
(g ⊢ bind v B : eUni U) ->
(g ⊢ v : A) ->
(g ⊢ A : eUni U') ->
forall x, exists A', ((g & x ~ Def v A') ⊢ open x B: eUni U).
Proof. intros. destruct B.
+ names in H. destruct x0.
  ++ names in H. names.
    cut ((@eId 0 (@free 0 (shift_name x name))) = ([^x] @eId 0 (@free 0 name))).
    - intros. rewrite H2. rewrite <- shift_uni_id with (x:=x).
      exists A. eapply cons_weakening_def. auto. eauto. auto.
    - names. auto.
  ++ destruct l.
    - names. names in H. exists (eUni U). apply aT_Var. 
      apply Types_only_if_wellformed in H0 as H2. 
      pose universe_common_parent. destruct e with (U:=U) (U':=U) (g:=g).
      auto. destruct H3. eapply wf_Def. auto. apply H3. 
      apply H.
      unfold assumes. right. exists ([^x] v).
      apply ctx_has.
    - names. names in H. exists A. 
    cut (eId (bound s) = ([^x] eId (bound s))); auto.
     * intros. simpl (0 + 0) in H2. rewrite H2.
       rewrite <- shift_uni_id with (x:=x).
       eapply cons_weakening_def.
       auto. apply H1. apply H0.
+ exists A. names. names in H.
 rewrite <- (shift_uni_id x U). 
 rewrite <- shift_uni_id with (x:=x).
    Check cons_weakening_def. 
    apply cons_weakening_def with U'; auto.
+ names. names in H.


Lemma substitution_assumption:
forall g v A B U, 
(g ⊢ v : A) ->
(g ⊢ bind v B : eUni U) ->
forall x, ((g & x ~ Assum A) ⊢ open x B: eUni U).
Proof. intros. inversion H0.
+ subst.
  

Lemma assumption_substitution:
forall g v A B U, 
(g ⊢ v : A) ->
forall x, ((g & x ~ Assum A) ⊢ open x B: eUni U) ->
(g ⊢ bind v B : eUni U).
Proof. Admitted.

Lemma Type_well_typed (g: env) (N: exp) (A: exp) :
  (g ⊢ N : A) ->
  exists U , Types g A (eUni U).
Proof.
  induction 1; eauto.
  - intros. destruct H0.
    + apply WellFormed_implies_well_typed_assum with (v:=x); auto.
    + destruct H0 as [e]. apply WellFormed_implies_well_typed_def with (v:=x) (e:=e); auto.
  - destruct IHTypes1, IHTypes2. cut (exists i, (g ⊢ (eUni x): (eUni (uType i))) /\ (g ⊢ (eUni x0): (eUni (uType i)))).
    + intro. destruct H3. exists (uType x1). apply aT_Sig with (x:="sigx").
      * eapply aT_Conv. eauto. eauto. destruct H3. apply universe_type_if. auto.
      * destruct H3. Check cons_weakening_assum. cut (g & "sigx" ~ Assum A ⊢ eUni x0 : eUni (uType x1)). 
        -- intro. apply substitution_assumption with (v:=v1). auto. 
            eapply aT_Conv. eauto. eauto. apply universe_type_if. auto.
        -- Check cons_weakening_assum. apply cons_weakening_assum with (B:=A) (U:=x) (A:=eUni x0) (A':=eUni (uType x1)) (x:="sigx"). auto. auto. 
    + apply universe_common_parent_type. eauto.
  - destruct IHTypes1. destruct IHTypes2. destruct x1.
    + exists uProp. eapply aT_Prod_Prop. eauto. eauto.
    + pose universe_common_parent_type. specialize e0 with (U:=uType i) (U':=uType i0) (g:=g). destruct e0. eauto. destruct H3.
      exists (uType x1). eapply aT_Prod_Type with (x:=x).
        * eapply aT_Conv. eauto. eauto. apply universe_type_if. auto.
        * eapply cons_weakening_assum with (B:=A) (x:=x) in H4. names in H4. eapply aT_Conv; eauto. apply universe_type_if. auto. eauto.
  -  Admitted. (*  apply WellFormed_implies. intros. induction H0.
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
  intros.  apply Type_well_typed in H as H1; auto. destruct H1.
  apply wf_Def with (U := x0); auto.
Qed.

Lemma append_env_weakening (g g': env):
  exists r, relates g' r (core.append g g').
Proof.
induction g.
+ exists r_id. cbn. apply ctx_id.
+ cbn. destruct IHg as [r]. exists (r,,^a)%ren. apply ctx_shift. auto.
Qed.

Lemma append_env_equiv_weakening (g g': env) (e e' : exp):
  Equiv g e e' ->
  Equiv (core.append g g') e e'.
Proof.
Admitted.

(*
Lemma append_env_weakening (g g': env) (N A : exp):
  Types g N A ->
  Types (core.append g g') N A.
Proof.
intros. 

Lemma append_env_equiv_weakening (g g': env) (e e' : exp):
  Equiv g e e' ->
  Equiv (append g g') e e'.
Proof.
Admitted. *)

Definition gbad:=
(ctx_empty & "e" ~ (Assum (eEqv eTru eFls))
& "P" ~ (Assum (ePi eBool (eUni (uType 0))))
& "f" ~ (Assum (ePi (eApp (eId (free "P")) eTru) eBool))
& "x" ~ (Assum (eApp (eId (free "P")) eFls))).

Lemma gbad_wf: WellFormed gbad. Admitted.

Lemma bad2:
forall g ->
WellFormed g ->
forall e P f x, 
Types g e (eEqv eTru eFls) ->
Types g P 

Lemma bad1: 
let expr:=(@eAbs 0 (eEqv eTru eFls) (eApp ((eId (free "f"))) (eId (free "x"))))
in 
(Types gbad
(eApp expr (eId (free "e"))) (bind expr eBool)).
Proof. intros. unfold expr. apply aT_App with (A' := (eEqv eTru eFls)). 
+ apply aT_Lam with (x:="z") (i:=0).
  - apply aT_Equiv with (B:=eBool).
    * apply aT_True. apply gbad_wf.
    * apply aT_False. apply gbad_wf.
    * apply aT_Bool. apply gbad_wf.
  - 


(* /\
(Reduces (ctx_empty & e ~ (Assum (eEqv eTru eFls))
& P ~ (Assum (ePi eBool (eUni (uType 0))))
& f ~ (ePi (eApp P eTru) eBool
& x ~ (P eFls))) (eApp (eAbs (eEqv t u) (f x)) e) (f e)).
 *)



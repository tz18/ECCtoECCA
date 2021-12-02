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
+  intros. names. apply aT_Pair with (x:=x) (Ua:=Ua) (Ub:= Ub).
  - auto.
  - specialize IHpT2 with (r:=r) (Δ:=Δ). names in IHpT2. apply IHpT2; eauto.
  - specialize IHpT3 with (r:=r) (Δ:=Δ). names in IHpT3. apply IHpT3; eauto.
  - names in IHpT4. names. specialize IHpT4 with (r:=(r ,, x)%ren) (Δ:=Δ & x ~ Assum ([r] A)). apply IHpT4.
    apply ctx_rename. auto. 
    apply Types_only_if_wellformed in pT3.
    apply wf_Assum with Ua; auto. apply IHpT3; eauto.
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
  - names. specialize IHpT3 with (Δ:= (Δ & p ~ (Eqv ([r] e) eTru))) (r:= (r,, p)%ren). names in IHpT3. apply IHpT3.
    apply ctx_rename. auto. eapply wf_Eqv; eauto.
  - names. specialize IHpT4 with (Δ:= (Δ & p ~ (Eqv ([r] e) eFls))) (r:= (r,, p)%ren). names in IHpT4. apply IHpT4.
    apply ctx_rename. auto. eapply wf_Eqv; eauto.
+ intros. apply aT_Conv with (A:=[r]A)(U:=U); eauto.
  apply SubTypes_weakening with g; auto.
+  intros. names. apply aT_App with ([r]A').
  - apply IHpT1; auto.
  - apply IHpT2; auto.
+ intros. names. apply aT_Fst with ([r]B). apply IHpT; auto.
+ intros. names. apply aT_Snd with ([r]A). apply IHpT; auto.
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

Lemma cons_weakening_eqv (g: env) (A A': exp) (x: name):
(g ⊢ A : A') ->
  (forall B i e e', 
   (g ⊢ e: B) ->
   (g ⊢ e': B) ->
   (g ⊢ B : (eUni (uType i))) ->
   (g & x ~ Eqv e e' ⊢ [^x] A : [^x] A')).
Proof.
intros. apply Type_weakening with g; auto. apply ctx_shift; apply ctx_id.
apply wf_Eqv with B i; auto. apply Types_only_if_wellformed with A A'; auto.
Qed.

Lemma rw_shiftv_shift_name {V} x x0: 
(@free V (shift_name x x0)) = shiftv x (@free V x0).
Proof. names. auto. Qed.

(* Lemma has_rest_2 g x x0 C B:
assumes (g & x ~ C) (free (shift_name x x0)) B ->
exists B', B = [^x] B'.
Proof.
intros. destruct H. rewrite rw_shiftv_shift_name in H. apply has_rest in H.
destruct H. destruct H. cut (exists B', x1 = Assum B').
  - intros. destruct H1. subst. names in H. exists x2. inversion H. auto.
  - destruct x1; try discriminate.
  -

Lemma cons_strengthening_assum g x x0 C B:
assumes (g & x ~ C) (free (shift_name x x0)) B ->
exists B', B = [^x] B'.
Proof.
intros. destruct H.

assumes g (free x0) B
 *) 
Lemma well_typed_cons g x thing:
(⊢ g & x ~ thing) -> ⊢ g.
Proof.
intros. inversion H; auto.
Qed.

Require Import String.
Open Scope string.

(* Lemma WF_1: 
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
Qed. *)

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

Lemma rename_uni_id:
forall r U {V},
([r] (@eUni V U)) = (@eUni V U).
Proof. auto. Qed.

Lemma open_uni_id:
forall x U {V},
(open x (@eUni (S V) U)) = (@eUni V U).
Proof. auto. Qed.

Lemma bind_uni_id: 
forall n U {V},
(bind n (@eUni (S V) U) = (@eUni V U)).
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
    eauto. eauto. unfold apply in H3. destruct c'. eauto. discriminate. discriminate.
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
    all: eauto. unfold apply in H6. destruct c'. eauto. discriminate. discriminate. unfold has. rewrite H5. auto.
+ intros. apply has_inversion in H3. apply get_inversion in H3.
  destruct H3. destruct H3. destruct H4. destruct H4. destruct H4. destruct H4.
  * inversion H4. subst. discriminate.
  * destruct H4. destruct H4. destruct H4. destruct H4. destruct H4. destruct H4.
    destruct H5. destruct H6. inversion H4. symmetry in H9, H10, H11. subst.
    cut (has g x4 x5). cut (exists B, x5 = Assum B).
    intros. destruct H3 as [B']. subst. names in H7. inversion H7. subst.
    apply IHWellFormed in H8. destruct H8. exists x1.
    rewrite <- shift_uni_id with (x:=x). 
    apply cons_weakening_eqv with (B:=B) (i:=i); auto.
    - unfold apply in H7. destruct x5; try discriminate. eauto.
    - apply has_inversion. auto.
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
    eauto. eauto. unfold apply in H3. destruct c'; try discriminate. eauto.
    apply has_inversion. eauto.
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
    unfold apply in H6. destruct c'; try discriminate. eauto.
    unfold has. rewrite H5. auto.
+ intros. apply has_inversion in H3. apply get_inversion in H3.
  destruct H3. destruct H3. destruct H4. destruct H4. destruct H4. destruct H4.
  * inversion H4. subst. discriminate.
  * destruct H4. destruct H4. destruct H4. destruct H4. destruct H4. destruct H4.
    destruct H5. destruct H6. inversion H4. symmetry in H9, H10, H11. subst.
    cut (has g x4 x5). cut (exists e' A0', x5 = Def e' A0').
    intros. destruct H3 as [e' [A0']]. subst. names in H7. inversion H7. subst.
    apply IHWellFormed in H8. destruct H8. exists x1.
    rewrite <- shift_uni_id with (x:=x). 
    apply cons_weakening_eqv with (B:=B) (i:=i); auto.
    - unfold apply in H7. destruct x5; try discriminate. eauto.
    - apply has_inversion. auto.
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

(*Lemma substitution_definition:
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
(* Lemma substitution_definition:
forall (B: @exp 1) g v A U U' C, 
(g ⊢ bind v B : C) ->
(g ⊢ v : A) ->
(g ⊢ A : eUni U') ->
(g ⊢ C : eUni U) ->
forall x, exists A', ((g & x ~ Def v A') ⊢ open x B: [^x] C).
Proof. induction B using term_ind_V; intros.
+ names in H. destruct v.
  ++ names in H. names.
    cut ((@eId 0 (@free 0 (shift_name x name))) = ([^x] @eId 0 (@free 0 name))).
    - intros. rewrite H3.
      exists A. eapply cons_weakening_def. auto. eauto. auto.
    - names. auto.
  ++ destruct l.
    - names. names in H. exists C. apply aT_Var. 
      apply Types_only_if_wellformed in H0 as H3. 
      eapply wf_Def. auto. apply H2. 
      apply H.
      unfold assumes. right. exists ([^x] v0).
      apply ctx_has.
    - names. names in H. exists A. 
    cut (eId (bound s) = ([^x] eId (bound s))); auto.
     * intros. simpl (0 + 0) in H2. rewrite H3.
       eapply cons_weakening_def.
       auto. apply H1. apply H0.
+ exists A. names. names in H. 
  rewrite <- shift_uni_id with (x:=x).
  apply cons_weakening_def with U'; auto.
+ names. names in H. 
  cut ((@eTru 0) = ([^x] @eTru 0)); auto. intro. 
  exists A. rewrite H3.
  apply cons_weakening_def with U'; auto.
+ names. names in H. 
  cut ((@eFls 0) = ([^x] @eFls 0)); auto. intro. 
  exists A. rewrite H3.
  apply cons_weakening_def with U'; auto.
+ names. names in H. 
  cut ((@eBool 0) = ([^x] @eBool 0)); auto. intro. 
  exists A. rewrite H3.
  apply cons_weakening_def with U'; auto.
+ names. names in H0. inversion H0. subst.
  exists A. apply aT_Lam.
 

(*Need to generalize from eUni U to C*)
Lemma substitution_definition:
forall g v A (B: @exp 1) U U', 
(g ⊢ bind v B : eUni U) ->
(g ⊢ v : A) ->
(g ⊢ A : eUni U') ->
forall x, exists A', ((g & x ~ Def v A') ⊢ open x B: eUni U).
Proof. intros. induction B using term_ind_V.
+ names in H. destruct v0.
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
    apply cons_weakening_def with U'; auto.
+ names. names in H. 
  rewrite <- shift_uni_id with (x:=x).
  cut ((@eTru 0) = ([^x] @eTru 0)); auto. intro. 
  exists A. rewrite H2.
  apply cons_weakening_def with U'; auto.
+ names. names in H. 
  rewrite <- shift_uni_id with (x:=x).
  cut ((@eFls 0) = ([^x] @eFls 0)); auto. intro. 
  exists A. rewrite H2.
  apply cons_weakening_def with U'; auto.
+ names. names in H. 
  rewrite <- shift_uni_id with (x:=x).
  cut ((@eBool 0) = ([^x] @eBool 0)); auto. intro. 
  exists A. rewrite H2.
  apply cons_weakening_def with U'; auto.
+ names. names in H. inversion H. subst.  *)


Lemma diamond_property_of_subtypes g e A B:
(g ⊢ e: A) ->
(g ⊢ e: B) ->
exists C, 
(g ⊢ C ≲ A) /\ (g ⊢ C ≲ B) /\ (g ⊢ e : C).
Proof.
intros. induction e using term_ind.
+ inversion H. 
  - subst. inversion H0.
    *  subst. Admitted.


(*(* 
Lemma :
 (g ⊢ eUni U ≲ A) ->
 (g ⊢ A: eUni U') ->
 (g ⊢ e: A) ->
 (g ⊢ e: eUni U'). *)

Lemma substitution_assumption:
forall g v A B U U' , 
(g ⊢ v : A) ->
(g ⊢ A : eUni U') ->
(g ⊢ bind v B : bind v C) ->
forall x, exists U'', ((g & x ~ Assum A) ⊢ open x B: open x C).
Proof. induction B using term_ind_V; intros.
+ names in H1. destruct v0.
  ++ names in H1. names.
    cut ((@eId 0 (@free 0 (shift_name x name))) = ([^x] @eId 0 (@free 0 name))).
    - intros. rewrite H2. exists U.  rewrite <- shift_uni_id with (x:=x).
      apply cons_weakening_assum with (U:=U'). auto. eauto.
    - names. auto.
  ++ destruct l.
    - names. names in H1. apply exp_types_must_subtype with (e:=v) (A:=A) in H1; auto.
      cut (⊢ g & x ~ Assum A); eauto; intros.
      destruct universe_common_parent with (U:=U) (U':=U) (g:=(g & x ~ Assum A)); auto.
      destruct H1.
        * exists U. eapply aT_Conv with (A:=[^x] A).
          -- apply aT_Var; auto. 
             left. apply ctx_has.
          -- destruct H3. apply t.
          -- rewrite <- shift_uni_id with (x:=x). apply SubTypes_weakening with (Γ:=g). auto. auto with contexts.
        * admit.
     - names. names in H. exists U. 
    cut (eId (bound s) = ([^x] eId (bound s))); auto.
     * intros. simpl (0 + 0) in H2. rewrite H2. rewrite <- shift_uni_id with (x:=x).
       eapply cons_weakening_assum.
       auto. apply H0.
+ exists U0. names. names in H. 
  rewrite <- shift_uni_id with (x:=x). rewrite <- shift_uni_id with (x:=x) (U:= U0).
  apply cons_weakening_assum with (U:=U'); auto.
+ exists U. names. names in H. 
  rewrite <- shift_uni_id with (x:=x).
  cut ((@eTru 0) = ([^x] @eTru 0)); auto; intro.
  rewrite H2.
  apply cons_weakening_assum with (U:=U'); auto.
+ exists U. names. names in H. 
  rewrite <- shift_uni_id with (x:=x).
  cut ((@eFls 0) = ([^x] @eFls 0)); auto; intro.
  rewrite H2.
  apply cons_weakening_assum with (U:=U'); auto.
+ exists U. names. names in H. 
  rewrite <- shift_uni_id with (x:=x).
  cut ((@eBool 0) = ([^x] @eBool 0)); auto; intro.
  rewrite H2.
  apply cons_weakening_assum with (U:=U'); auto.
+ names. names in H2. inversion H2. subst.
  exists U. (* apply aT_Conv. *)
  Admitted.
  

Lemma assumption_substitution:
forall g v A B U, 
(g ⊢ v : A) ->
forall x, ((g & x ~ Assum A) ⊢ open x B: eUni U) ->
(g ⊢ bind v B : eUni U).
Proof. Admitted.

(* Lemma substitution_assumption:
forall g v A B U U' , 
(g ⊢ v : A) ->
(g ⊢ bind v B : eUni U) ->
exists A, forall x,
(g ⊢ A : eUni U') ->
(g ⊢ v : A) ->
((g & x ~ Assum A) ⊢ open x B: eUni U).
Proof. Admitted. *) *)

Compute 1 + 1. (* Phew *)

Inductive name_irrelevant {V} : @exp V -> Prop:=
| uni_ni (U: universe):
  name_irrelevant (eUni U)
| tru_ni: 
  name_irrelevant eTru
| fls_ni: 
  name_irrelevant eFls
| bool_ni:
  name_irrelevant eBool.
Hint Constructors name_irrelevant.

Lemma unopen_ni {V} (e: @exp V) x P:
name_irrelevant e ->
e = open x P ->
P = (wk e).
Proof. intros. cbn in P. cbn. destruct H; destruct P; try discriminate; names in H0; symmetry in H0; names; auto.
-   cut (forall U, ((@eUni (S V) U) = (wk (@eUni V U)))).
  + intro. rewrite H. rewrite H0. rewrite H. auto.
  + auto.
Qed.


Lemma unopen_id {V} x0 x (P: @exp (S V)):
@eId V x0 = open x P->
match x0 with
| bound l => P = eId (@bound (S V) (lS l)) /\ x0 = (bound l)
| free y' => (exists y, P = eId (free y) /\ y' = (shift_name x y)) \/
             (P = (@eId (S V) (@bound (S V) l0)) /\ x0 = (free x))
end.
Proof. intros.
destruct x0.
+ destruct P; try discriminate. destruct x0.
  - induction (compare_names name0 x).
    * names in H. left. exists name0. inversion H. auto.
    * inversion H. left. names in H. exists name0. auto.
  - right. names in H. inversion H. destruct l.
    * names in H1. auto.
    * discriminate.
+ destruct P; try discriminate.
  destruct x0; try discriminate. names in H. unfold openv in H. cbn in H. destruct l0; try discriminate.
  inversion H. subst. auto.
Qed.

Require Import Coq.Program.Equality.

Lemma luo_cut_assum_2 g P A:
(g ⊢ P : A) ->
forall x N,
(g ⊢ eId (free x) : N) ->
forall M,
((g ⊢ M : N) ->
(g ⊢ [M // x] P :[M // x] A)).
Proof.
intros. induction H; names; eauto.

Lemma luo_cut_assum g x N P A:
(g & x ~ Assum N ⊢ P : A) ->
forall M,
((g ⊢ M : N) ->
(g ⊢ [M // x] P :[M // x] A)).
Proof.
intro. dependent induction H. 
+ eauto.
+ intros. names. eauto.
+ shelve. (* intros. subst. destruct (compare_vars x x0).
  - names. destruct H0.
    -- apply has_first in H0. names in H0. inversion H0. names. auto.
    -- destruct H0. apply has_first in H0. discriminate.
  - names. destruct H0. 
    -- apply has_rest in H0. destruct H0. destruct H0. destruct x0; try discriminate. names in H0. inversion H0. names.
       eauto.
    -- destruct H0. apply has_rest in H0. destruct H0. destruct H0. destruct x1; try discriminate.
       names in H0. inversion H0. names. apply aT_Var. eauto. eauto.
 *)+ eauto.
+ eauto.
+ eauto.
+ intros. 
  names.
  apply aT_Sig with (x:=x0). 
  - (* apply IHTypes1; auto. *) shelve.
  - apply IHTypes2 with (x1:=x) in H1.  


with (g0:=g & x ~ Assum N). names.  
    (g0:=(g & x ~ Assum N)) (P:=B) (A:=eUni (uType i)). names.
  forall r Δ,
    Γ =[r]=> Δ ->
    (⊢ Δ) ->
    (Δ ⊢ ([r] e) : [r] A). 
+ Admitted.
(* 
  apply aT_Sig with (x:=x0). 
  - apply IHTypes1 with (N0:=N); auto.
  - specialize IHTypes2 with (x1:= x0) (N0:=A).
    specialize IHTypes2 with (g0:=g & x ~ Assum N). names.  
    (g0:=(g & x ~ Assum N)) (P:=B) (A:=eUni (uType i)). names.
  forall r Δ,
    Γ =[r]=> Δ ->
    (⊢ Δ) ->
    (Δ ⊢ ([r] e) : [r] A). 

Lemma luo_cut_assum g x N P A:
(g & x ~ Assum N ⊢ (open x P) : (open x A)) ->
forall M,
((g ⊢ M : N) ->
(g ⊢ bind M P : (bind M A))).
Proof.
intro. dependent induction H.
+ subst. rename x1 into HeqP0. rename x into HeqA0. apply unopen_ni in HeqP0; auto. apply unopen_ni in HeqA0; auto. rewrite HeqP0. rewrite HeqA0. names.
  eauto.
+ subst. rename x1 into HeqP0. rename x into HeqA0. apply unopen_ni in HeqP0; auto. apply unopen_ni in HeqA0; auto. rewrite HeqP0. rewrite HeqA0. names.
  eauto.
+ rename H0 into H1. intros. subst. rename x into HeqP0. apply unopen_id in HeqP0. destruct x0.
  - destruct HeqP0.
    ++ destruct H2. destruct H2. subst. names.
    apply aT_Var. apply well_typed_cons in H; auto. rewrite rw_shiftv_shift_name in H1. destruct H1. 
      * apply has_rest in H1. destruct H1. destruct H1. destruct x0; try discriminate. names in H1.
        inversion H1. apply (f_equal (close x1)) in H4. names in H4. rewrite H4. names. auto.
      * destruct H1. apply has_rest in H1. destruct H1. destruct H1. destruct x2; try discriminate.
        names in H1. unfold assumes. right. exists e. inversion H1. apply (f_equal (close x1)) in H5.
        names in H5. rewrite H5. names. auto.
    ++ destruct H2. subst. rewrite H3 in H1. destruct H1.
       -- apply has_first in H1. names. names in H1. inversion H1. 
          apply (f_equal (close x1)) in H4. names in H4. rewrite H4. names. auto.
       -- destruct H1. remember (Def x (open x1 A)) as B. apply has_first in H1. subst. discriminate. 
  - destruct HeqP0. subst. names. destruct H1.
    ++ apply has_inversion in H1. apply get_inversion in H1. destruct H1. destruct H1. discriminate.
    ++ destruct H1. apply has_inversion in H1. apply get_inversion in H1. destruct H1. destruct H1. discriminate.
+ subst. rename x1 into HeqP0. rename x into HeqA0. apply unopen_ni in HeqP0; auto. apply unopen_ni in HeqA0; auto. rewrite HeqP0. rewrite HeqA0. names.
  eauto.
+ subst. rename x1 into HeqP0. rename x into HeqA0. apply unopen_ni in HeqP0; auto. apply unopen_ni in HeqA0; auto. rewrite HeqP0. rewrite HeqA0. names.
  eauto.
+ subst. rename x1 into HeqP0. rename x into HeqA0. apply unopen_ni in HeqP0; auto. apply unopen_ni in HeqA0; auto. rewrite HeqP0. rewrite HeqA0. names.
  eauto.
+ subst. intros. rename x2 into HeqP0. rename x into HeqA0.
  rename x1 into x. apply (f_equal (close x)) in HeqP0.
  names in HeqP0. apply unopen_ni in HeqA0.
  subst. names in IHTypes2. names in IHTypes1. cbn.
  apply aT_Sig with (x:=x). 
  - apply IHTypes1 with (P:=(close x A0)) (x0:=x) (A:= eUni (uType i)) (g0:=g) (N0:=N);
    names; eauto. 
  - specialize IHTypes2 with (x1:= x0) (N0:=A0) 
    (g0:=(g & x ~ Assum N)) (P:=B) (A:=eUni (uType i)). names.
  
apply IHTypes1.

Admitted.

 *)
(* 
Lemma luo_cut_assum g x N P A:
(g & x ~ Assum N ⊢ (open x P) : (open x A)) ->
forall M,
((g ⊢ M : N) ->
(g ⊢ bind M P : (bind M A))).
Proof.
intro. remember (g & x ~ Assum N) as g0 in H. remember (open x P) as P0 in H.
 remember (open x A) as A0 in H. induction H.
+ subst. apply unopen_ni in HeqP0; auto. apply unopen_ni in HeqA0; auto. rewrite HeqP0. rewrite HeqA0. names.
  eauto.
+ subst. apply unopen_ni in HeqP0; auto. apply unopen_ni in HeqA0; auto. rewrite HeqP0. rewrite HeqA0. names.
  eauto.
+ rename H0 into H1. intros. subst. apply unopen_id in HeqP0. destruct x0.
  - destruct HeqP0.
    ++ destruct H2. destruct H2. subst. names.
    apply aT_Var. apply well_typed_cons in H; auto. rewrite rw_shiftv_shift_name in H1. destruct H1. 
      * apply has_rest in H1. destruct H1. destruct H1. destruct x1; try discriminate. names in H1.
        inversion H1. apply (f_equal (close x)) in H4. names in H4. rewrite H4. names. auto.
      * destruct H1. apply has_rest in H1. destruct H1. destruct H1. destruct x2; try discriminate.
        names in H1. unfold assumes. right. exists e. inversion H1. apply (f_equal (close x)) in H5.
        names in H5. rewrite H5. names. auto.
    ++ destruct H2. subst. rewrite H3 in H1. destruct H1.
       -- apply has_first in H1. names. names in H1. inversion H1. 
          apply (f_equal (close x)) in H4. names in H4. rewrite H4. names. auto.
       -- destruct H1. remember (Def x0 (open x A)) as B. apply has_first in H1. subst. discriminate. 
  - destruct HeqP0. subst. names. destruct H1.
    ++ apply has_inversion in H1. apply get_inversion in H1. destruct H1. destruct H1. discriminate.
    ++ destruct H1. apply has_inversion in H1. apply get_inversion in H1. destruct H1. destruct H1. discriminate.
+ subst. apply unopen_ni in HeqP0; auto. apply unopen_ni in HeqA0; auto. rewrite HeqP0. rewrite HeqA0. names.
  eauto.
+ subst. apply unopen_ni in HeqP0; auto. apply unopen_ni in HeqA0; auto. rewrite HeqP0. rewrite HeqA0. names.
  eauto.
+ subst. apply unopen_ni in HeqP0; auto. apply unopen_ni in HeqA0; auto. rewrite HeqP0. rewrite HeqA0. names.
  eauto.
+ subst. intros. apply (f_equal (close x)) in HeqP0. names in HeqP0. apply unopen_ni in HeqA0. subst. names. names in IHTypes2. names in IHTypes1.
  apply aT_Sig with (x:=x). 
 
Admitted.
*)
(* Lemma luo_cut_assum_wrong x f M:
(((ctx_empty & f ~ (Assum (ePi eBool (eEqv eBool (ePi eBool eBool))))) & x ~ (Assum (eEqv eBool (ePi eBool eBool)))) ⊢ (open x eTru) : (open x (ePi eBool eBool))) ->
((ctx_empty & f ~ (Assum (ePi eBool (eEqv eBool (ePi eBool eBool))))) ⊢ (eApp (eId (free f)) eTru) : (eEqv eBool (ePi eBool eBool))) ->
((ctx_empty & f ~ (Assum (ePi eBool (eEqv eBool (ePi eBool eBool))))) ⊢ bind M (eTru) : (bind M (ePi eBool eBool))).
Proof. *)

Lemma luo_cut_def g x N P A M:
(g & x ~ Def M N ⊢ open x P : open x A) ->
(g ⊢ bind M P : (bind M A)).
Proof.
intros.
Admitted. 

Corollary luo_cut_assum_opened g x N P A:
(g & x ~ Assum N ⊢ (open x P) : (open x A)) ->
forall M,
((g ⊢ M : N) ->
(g ⊢ bind M P : (bind M A))).
Proof.
intros. 
remember (open x P) as B1.
apply (f_equal (close x)) in HeqB1. 
remember (open x A) as C1.
apply (f_equal (close x)) in HeqC1.
names in HeqB1. names in HeqC1.
rewrite <- HeqB1. rewrite <- HeqC1.
names. apply luo_cut_assum with (N:=N); eauto.
Qed.

Require Import Coq.Program.Equality.
Lemma well_typed_app g A' B e' x:
(g ⊢ ePi A' B : eUni x) ->
(g ⊢ e' : A') ->
exists U : universe, (g ⊢ bind e' B : eUni U).
Proof. intro. dependent induction H; try discriminate.
+ exists uProp. rewrite <- bind_uni_id with (n:=e').
  apply luo_cut_assum_opened with x0 A'; eauto.

+ exists (uType i). rewrite <- bind_uni_id with (n:=e').
  apply luo_cut_assum_opened with x0 A'; eauto.
+ intros. apply IHTypes1 with (A'0:=A') (x:=x). Admitted. 

Lemma Type_well_typed (g: env) (N: exp) (A: exp) :
  (g ⊢ N : A) ->
  exists U , Types g A (eUni U).
Proof.
  induction 1; eauto.
  - intros. destruct H0.
    + apply WellFormed_implies_well_typed_assum with (v:=x); auto.
    + destruct H0 as [e]. apply WellFormed_implies_well_typed_def with (v:=x) (e:=e); auto.
  - destruct IHTypes1, IHTypes2, IHTypes3, IHTypes4. 
    (* apply substitution_assumption with (A:=A) (U':= x) (x:="sigx") in H2 as H9; auto.
    destruct H9.*)
    cut (exists i, (g ⊢ (eUni Ua): 
          (eUni (uType i))) /\ (g ⊢ (eUni Ub): (eUni (uType i)))); intros.
    + destruct H7. exists (uType x4). apply aT_Sig with (x:=x).
      * eapply aT_Conv. apply H1. eauto. destruct H7. apply universe_type_if. auto.
      * destruct H7. cut (g & x ~ Assum A ⊢ eUni Ub : eUni (uType x4)); intros.
        -- eapply aT_Conv. eauto. eauto. apply universe_type_if. auto.  
        -- Check  cons_weakening_assum. 
           apply cons_weakening_assum with (B:=A) (U:=Ua) (A:=eUni Ub) (A':=eUni (uType x4)) (x:=x). 
           auto. auto. 
    + apply universe_common_parent_type. eauto.
  - destruct IHTypes1. destruct IHTypes2. destruct x1.
    + exists uProp. eapply aT_Prod_Prop. eauto. eauto.
    + pose universe_common_parent_type. specialize e0 with (U:=uType i) (U':=uType i0) (g:=g). destruct e0. eauto. destruct H3.
      exists (uType x1). eapply aT_Prod_Type with (x:=x).
        * eapply aT_Conv. eauto. eauto. apply universe_type_if. auto.
        * eapply cons_weakening_assum with (B:=A) (x:=x) in H4. names in H4. 
          eapply aT_Conv; eauto; apply universe_type_if; auto; eauto. eauto.
  - destruct IHTypes1. destruct IHTypes2. destruct IHTypes3. exists x2.
    rewrite <- bind_uni_id with (n:=n).
    apply luo_cut_def with (x:=x) (N:=A).
    rewrite open_uni_id.
    auto.
  - destruct IHTypes1. destruct IHTypes2. destruct IHTypes3. destruct IHTypes4.
    exists U. rewrite <- bind_uni_id with (n:=e).
    apply luo_cut_assum_opened with (x:=x) (N:= eBool). auto. auto.
  - destruct IHTypes1. inversion H1; subst.
    + exists uProp. rewrite <- bind_uni_id with (n:=e').
      apply luo_cut_assum_opened with (x:=x0) (N:=A'); auto.
    + exists (uType i). rewrite <- bind_uni_id with (n:=e').
      apply luo_cut_assum_opened with (x:=x0) (N:=A'); auto.
    + Admitted. (*  apply WellFormed_implies. intros. induction H0.
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



Require Export reduction.

Open Scope ECCA_scope.

Lemma Steps_cons_shift: 
forall (Γ : context) (e1 e2: exp) (A: ctxmem) (x: name),
(Γ ⊢ e1 ⊳ e2) -> ((Γ & x ~ A) ⊢ ([^x] e1) ⊳ ([^x] e2)). 
Proof. intros. induction H; cbn; auto.
+ apply st_ID with (A:= [^x] A1). names. apply has_rest. exists (Def e' A1). names. auto.
+ names. auto.
+ names. auto.
Qed.

Lemma Steps_weakening:
forall (Γ: context) (e1 e2: exp), 
(Γ ⊢ e1 ⊳ e2) -> 
forall (Δ: context) (r: ren),
Γ =[r]=> Δ ->
(Δ ⊢ ([r] e1) ⊳ ([r] e2)).
Proof.
induction 1; cbn; auto.
+ intros. destruct H0. apply H0 in H. names in H. rewrite applyt_is_applyv with (rn:=total). names. 
  apply st_ID with (A:= [s] A0). auto.
+ intros. names. auto.
+ intros. names. auto.
Qed.
Hint Resolve Steps_weakening.


Lemma Reduces_weakening:
forall (Γ: context) (e1 e2: exp),
(Γ ⊢ e1 ⊳* e2) -> 
forall (Δ: context) (r: ren), 
Γ =[r]=> Δ ->
(Δ ⊢ ([r] e1) ⊳* ([r] e2)).
Proof. induction 1; cbn; auto.
+ intros. apply R_RedR. apply Steps_weakening with (Γ := g). auto. auto.
+ intros. apply R_Trans with (e':= [r] e'); auto.
+ intros. apply R_CongLet with (A:= [r] A0) (x:= x). auto. names. apply IHReduces2.
  apply ctx_rename. auto.
+ intros. apply R_CongLam1 with (A:= [r] A0) (x:= x). auto. names. apply IHReduces2.
  apply ctx_rename. auto.
+ intros. apply R_CongPi with (A:= [r] A0) (x:= x). auto. names. apply IHReduces2.
  apply ctx_rename. auto.
+ intros. apply R_CongSig with (A:= [r] A0) (x:= x). auto. names. apply IHReduces2.
  apply ctx_rename. auto.
Qed.
Hint Resolve Reduces_weakening.

(* Lemma Reduces_cons_shift:
    forall (Γ : context) (e1 e2: exp) (x: name) (A: ctxmem),
      (Γ ⊢ e1 ⊳* e2) -> ((Γ & x ~ A) ⊢ ([^x] e1) ⊳* ([^x] e2)).
Proof.
intros. apply Reduces_weakening with (Γ:= Γ).
apply ctx_shift; apply ctx_id. auto.
Qed. *)



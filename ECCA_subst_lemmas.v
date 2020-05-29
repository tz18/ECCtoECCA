(* Require Export ECCA_subst.

Lemma notin_fv_equivariance : forall x0 x y t ,
  x0 `notin` FV t ->
  swap_var x y x0  `notin` FV (swap x y t).
Proof.
  induction t; intros; simpl in *.
  1-13: unfold swap_var in *; auto; default_simp.  
Qed.
Hint Resolve notin_fv_equivariance.

Lemma notin_fv_equivariance_easy (x y: atom) (b1 b2: ECCAexp):
(x `notin` FV b2 ->
y `notin` FV (swap y x b2))%ECCA.
Proof. intros. cut (y = (swap_var y x x)).
+ intros. rewrite H0 at 1. apply notin_fv_equivariance. assumption.
+ unfold swap_var. default_simp.
Qed.

Lemma in_fv_equivariance : forall x y x0 t,
  x0 `in` FV t ->
  swap_var x y x0 `in` FV (swap x y t).
Proof.
  (* ADMITTED *)
  induction t; intros; simpl in *.
  all: try (unfold swap_var; default_simp; fsetdec).
  all: destruct (AtomSetImpl.union_1 H); unfold swap_var in *; default_simp; fsetdec.
Qed. (* ADMITTED *)
Hint Resolve in_fv_equivariance.

Lemma swap_involutive : forall t x y,
    swap x y (swap x y t) = t.
Proof.
  (* ADMITTED *)
  induction t;  simpl; unfold swap_var; default_simp.
Qed.
Hint Resolve swap_involutive.

Lemma swap_id : forall n x,
    swap x x n = n.
Proof.
  induction n; simpl; unfold swap_var;  default_simp.
Qed.
Hint Resolve swap_id.

Lemma swap_symmetric : forall t x y,
    swap x y t = swap y x t.
Proof.
  induction t;  simpl; unfold swap_var; default_simp.
Qed. 
Hint Resolve swap_symmetric.

Lemma swap_var_equivariance : forall v x y z w,
    swap_var x y (swap_var z w v) =
    swap_var (swap_var x y z) (swap_var x y w) (swap_var x y v).
Proof.
  unfold swap_var; default_simp.
Qed.
Hint Resolve swap_var_equivariance.

Lemma swap_equivariance : forall t x y z w,
    swap x y (swap z w t) = swap (swap_var x y z) (swap_var x y w) (swap x y t).
Proof.
  induction t; intros; simpl; try rewrite swap_var_equivariance; try auto.
  1,2,3,5: rewrite swap_var_equivariance; rewrite IHt1; rewrite IHt2; auto.
  all: default_simp.
Qed.
Hint Resolve swap_equivariance.

Lemma subst_distributes_over_app (y: atom) (A B1 B2: ECCAexp) :
 subst y A (eApp B1 B2) = eApp (subst y A B1) (subst y A B2).
Proof.
- rewrite substWork_equation. case_eq (AtomSetImpl.mem y (FV (eApp B1 B2))).
  + intros. auto.
  + intros. default_simp.
    * cut (AtomSetImpl.mem y (FV B1) = false).
      -- intros. rewrite substWork_equation. rewrite H0. reflexivity. 
      -- rewrite <- not_mem_iff. rewrite <- not_mem_iff in H. fsetdec.
    * cut (AtomSetImpl.mem y (FV B2) = false).
      -- intros. rewrite substWork_equation. rewrite H0. reflexivity. 
      -- rewrite <- not_mem_iff. rewrite <- not_mem_iff in H. fsetdec.
 Qed.
Hint Resolve subst_distributes_over_app.
 *)
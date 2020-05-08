Require Export ECCA_equiv.
Require Import ECCA_subst_lemmas.
Require Import ECCA_reduction_lemmas.

Lemma equiv_refl (g: ECCAenv) (A: ECCAexp):
(g |- A =e= A)%ECCA.
Proof.
apply aE_Equiv with (e:= A); auto.
Qed.



Lemma aeq_fv_the_tough_part (x y : atom) (t1 t2 b1 b2 : ECCAexp)
(H : x `notin` FV b2)
(H0 : (b1 =a= swap y x b2)%ECCA)
(H1 : (t1 =a= t2)%ECCA)
(IHECCA_Aeq1 : FV b1 [=] FV (swap y x b2))
(IHECCA_Aeq2 : FV t1 [=] FV t2):
    union (FV t1) (remove x (FV b1)) 
[=] union (FV t2) (remove y (FV b2)).
Proof.
unfold AtomSetImpl.Equal.
    intro a.
    repeat rewrite union_iff; repeat rewrite remove_iff.
    rewrite IHECCA_Aeq1.
    rewrite IHECCA_Aeq2.
    split.
    + intros [K1 | K2] .
      * auto.
      * destruct K2. apply (in_fv_equivariance y x) in H2.
        rewrite swap_involutive in H2.
        unfold swap_var in H2.
        destruct (a == y); subst.
          -- contradiction.
          -- destruct (a == x); subst. 
            ++ contradiction.
            ++ right; split; auto.
    + intros [K1 | K2].
      * apply (in_fv_equivariance y x) in K1. 
        pose (J := notin_fv_equivariance x y x b2 H). clearbody J.
        unfold swap_var in *. destruct (a == y); subst.
        -- destruct (x == y); subst.
          ++ left. rewrite swap_id in K1. auto.
          ++ destruct (x == x); try contradiction. left.
              apply in_fv_equivariance with (x:= x) (y := y) in K1. 
              rewrite swap_symmetric in K1. rewrite swap_involutive in K1.
              unfold swap_var in K1. destruct (x == x) in K1; try contradiction.
              apply K1.
        -- destruct (a == x); destruct (x ==y); subst.
          ++ rewrite swap_id in K1. left. apply K1.
          ++ default_simp. left.
             apply in_fv_equivariance with (x:= x) (y := y) in K1.
             rewrite swap_symmetric in K1. rewrite swap_involutive in K1.
             unfold swap_var in K1. default_simp. 
          ++ rewrite swap_id in K1. left. apply K1.
          ++ destruct (x==x) in J; try contradiction. apply notin_fv_equivariance with (x:= x) (y := y) in J.
             rewrite swap_symmetric in J. rewrite swap_involutive in J.
             unfold swap_var in J. default_simp.
             apply in_fv_equivariance with (y:=x) (x:=y) in K1. 
             rewrite swap_involutive in K1. unfold swap_var in K1. default_simp.
      * right. destruct K2. split.
        -- apply in_fv_equivariance with (x:=y) (y:=x) in H2. unfold swap_var in H2.
           default_simp. apply in_fv_equivariance with (x:=y) (y:=x) in H2. 
           rewrite swap_involutive in H2. unfold swap_var in H2. default_simp.
        -- destruct (x==a). subst. contradiction. assumption.
Qed.

Lemma aeq_fv : forall t1 t2,
    (t1 =a= t2 ->
    FV t1 [=] FV t2)%ECCA.
Proof.
  induction 1; simpl in *; try fsetdec.
  all: apply aeq_fv_the_tough_part; assumption.
Qed.

Lemma aeq_equivariance : forall x y t1 t2,
    ECCA_Aeq t1 t2 ->
    ECCA_Aeq (swap x y t1) (swap x y t2).
Proof.
  induction 1; intros; simpl in *; auto.
  all: destruct (swap_var x y x0 == swap_var x y y0).
  1,3,5,7: rewrite e; eapply aeq_abs_same || eapply aeq_pi_same 
                   || eapply aeq_let_same || eapply aeq_sig_same;
   auto; rewrite swap_equivariance in IHECCA_Aeq1; 
   rewrite e in IHECCA_Aeq1; rewrite swap_id in IHECCA_Aeq1; auto.
  all: rewrite swap_equivariance in IHECCA_Aeq1; 
        eapply aeq_abs_diff || eapply aeq_pi_diff 
     || eapply aeq_let_diff || eapply aeq_sig_diff;
        try eapply notin_fv_nom_equivariance; auto.
Qed.

 Lemma aeq_sym_the_hard_part1
(x y : atom)
(t1 t2 b1 b2 : ECCAexp)
(H : x `notin` FV b2)
(H0 : (b1 =a= swap y x b2)%ECCA)
(IHECCA_Aeq1 : (swap y x b2 =a= b1)%ECCA):
y `notin` FV b1.
Proof.
apply notin_fv_equivariance_easy with (y:=y) in H. 
  rewrite aeq_fv with (t1 := b1) (t2 := swap y x b2); auto. auto.
Qed.

 Lemma aeq_sym_the_hard_part2
(x y : atom)
(t1 t2 b1 b2 : ECCAexp)
(H : x `notin` FV b2)
(H0 : (b1 =a= swap y x b2)%ECCA)
(IHECCA_Aeq1 : (swap y x b2 =a= b1)%ECCA):
(b2 =a= swap x y b1)%ECCA.
Proof.
eapply aeq_equivariance with (x:=x) (y:=y) in IHECCA_Aeq1.
  rewrite swap_symmetric in IHECCA_Aeq1.
  rewrite swap_involutive with (x:=y) (y:=x) in IHECCA_Aeq1. auto.
Qed.

Lemma aeq_sym (A B: ECCAexp):
(A =a= B ->
B =a= A)%ECCA.
Proof.
intros. induction H.
all: try auto.
all: apply aeq_abs_diff || apply aeq_pi_diff || apply aeq_let_diff || apply aeq_sig_diff ; auto.
all: apply aeq_sym_the_hard_part1 with (x:=x) (b2:=b2)
  || apply aeq_sym_the_hard_part2 with (x:=x) (b2:=b2); auto.
Qed.

Lemma equiv_sym (g: ECCAenv) (A B: ECCAexp):
((g |- A =e= B) ->
(g |- B =e= A))%ECCA.
Proof.
intros. inversion H.
- apply aE_Equiv with (e := e); auto.
- subst. eapply aE_EquivIta2.
  + auto.
  + apply H1.
  + apply H0.
  + apply H2.
- subst. eapply aE_EquivIta1.
  + auto.
  + apply H1.
  + apply H0.
  + apply H2.
- apply aE_EquivAlpha; apply aeq_sym; auto.
Qed.

Lemma equiv_trans (g: ECCAenv) (A B C: ECCAexp):
((g |- A =e= B) ->
(g |- B =e= C) ->
(g |- A =e= C))%ECCA.
Proof.
intros. induction H; induction H0; subst.
- cut (exists d, (g |- e =r> d) /\ (g |- e0 =r> d))%ECCA.
  + intros. destruct H3. destruct H3. apply aE_Equiv with (e:=x).
    * apply R_Trans with (e':=e); auto.
    * apply R_Trans with (e':=e0); auto.
  + apply church_rosser with (e:=e2); auto.
- cut (exists d, (g |- e =r> d) /\ (g |- (eAbs x A e2) =r> d))%ECCA.
  + intros. destruct H4. destruct H4.
(*need more church rosser stuff for the eta-equivalence cases.*)
Admitted.

(* 
Lemma equiv_distributes_over_pi (g: ECCAenv) (x: atom) (B B' A A': ECCAexp):
(g |- A =e= A' ->
g |- B =e= B' ->
g |- ePi x A B =e= ePi x A' B')%ECCA.
Proof.
intros. inversion H. inversion H0.
- subst.

Lemma equiv_equivariant_over_subst (g: ECCAenv) (x: atom) (N N' A B: ECCAexp):
(g |- N : A ->
g |- N' : A ->
g |- N =e= N' ->
g |- (subst x N B) =e= (subst x N' B)
)%ECCA.
Proof.
intros. induction H1. 
- rewrite substWork_equation. rewrite substWork_equation.
 destruct AtomSetImpl.mem.
  + induction B; auto. destruct (x == x0); auto.
    * eapply aE_Equiv with (e := e); auto.
    * destruct (x == x0).
      ++




  + destruct (x == x0).
    * apply H1.
    * auto.
  + destruct (x == x0).
    * auto. Reset IHB2. inversion IHB1. 
        --

   
- *)

Lemma ECCA_Aeq_equivariance : forall x y t1 t2,
    ECCA_Aeq t1 t2 ->
    ECCA_Aeq (swap x y t1) (swap x y t2).
Proof.
  induction 1; intros; simpl in *; auto.
  all: destruct (swap_var x y x0 == swap_var x y y0).
  1,3,5,7: rewrite e; eapply aeq_abs_same || eapply aeq_pi_same || eapply aeq_let_same || eapply aeq_sig_same;
   auto; 
   rewrite swap_equivariance in IHECCA_Aeq1; rewrite e in IHECCA_Aeq1; rewrite swap_id in IHECCA_Aeq1; auto.
  all: rewrite swap_equivariance in IHECCA_Aeq1; eapply aeq_abs_diff || eapply aeq_pi_diff || eapply aeq_let_diff || eapply aeq_sig_diff;
      try eapply notin_fv_nom_equivariance; auto.
Qed.

Lemma capture_avoid_is_aeq_abs (xnew x: atom) (fvarg: atoms) (A e: ECCAexp):
((let (xnew,_) := atom_fresh (union (fvarg) (FV e)) in
                    (eAbs xnew A (swap x xnew e)))
  =a=
eAbs x A e)%ECCA.
Proof.  destruct atom_fresh. intros. apply aeq_abs_diff.
- fsetdec.
- auto.
- auto.
Qed.

(* Lemma subst_over_swap (x y z: atom) (A B: ECCAexp):
(y <> x ->
z `notin` FV B ->
(subst y A B =a= B) ->
(subst y A (swap x z B) =a= swap x z B))%ECCA.
Proof.
intros. inversion H1. 
- subst. auto. rewrite H3.
Admitted. *)

Lemma subst_no_fv_aeq (y: atom) (A B: ECCAexp):
(y `notin` (FV B) ->
subst y A B =a= B)%ECCA.
Proof.
intros. rewrite not_mem_iff in H. rewrite substWork_equation. rewrite H. auto.
Qed.
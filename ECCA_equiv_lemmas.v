Require Export ECCA_equiv.
Require Import ECCA_reduction_lemmas.
Require Import Equivalence.

Lemma equiv_refl (g: ECCAenv): Reflexive (ECCA_Equiv g).
Proof.
unfold Reflexive. intros. eapply aE_Refl. 
Qed.

Lemma equiv_sym (g: ECCAenv): Symmetric (ECCA_Equiv g).
Proof.
  unfold Symmetric. intros. eapply aE_Symm. auto.
Qed.

Lemma equiv_trans (g: ECCAenv): Transitive (ECCA_Equiv g).
Proof.
  unfold Transitive. intros. eapply aE_Trans. apply H. auto.
Qed.

Lemma equiv_weakening (g: ECCAenv) (x: name) (a: ctxmem) (e1 e2: ECCAexp):
  (ECCA_Equiv g e1 e2) ->
  (ECCA_Equiv (ctx_cons g x a) e1 e2).
Admitted.

Instance ECCA_Equiv_equiv (g: ECCAenv) : Equivalence (ECCA_Equiv g).
Proof.
split. apply equiv_refl. apply equiv_sym. apply equiv_trans.
Qed.
Hint Resolve ECCA_Equiv_equiv.
Require Import String.

(*TODO: To use this, we need to declare some functions proper wrt to ECCA_equiv.
Then we can do rewriting. 
See page 17 of 
https://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf *)

(* Require Import ECCA_typing. *)

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
(* Lemma equiv_abs_compositional_1 (g: ECCAenv) (A A' b: ECCAexp): 
(ECCA_Equiv g A A') ->
(ECCA_Equiv g (eAbs A b) (eAbs A' b))%ECCA.
Proof.
intros. inversion H.
+ subst. apply aE_Equiv with (e:=eAbs e b); eapply R_CongLam1; auto.
Admitted.

Lemma equiv_abs_compositional_2 (g: ECCAenv) (x: atom) (A b b': ECCAexp): 
(ECCA_Equiv (Assum g x A) b b') ->
(ECCA_Equiv g (eAbs x A b) (eAbs x A b'))%ECCA.
Proof.
intros. induction H.
+ apply aE_Equiv with (e:=eAbs x A e); apply R_CongLam1; auto.
Admitted.

Lemma equiv_abs_compositional (g: ECCAenv) (x: atom) (A A' b b': ECCAexp): 
(ECCA_Equiv g A A') ->
(ECCA_Equiv (Assum g x A) b b') ->
(ECCA_Equiv g (eAbs x A b) (eAbs x A' b'))%ECCA.
Proof.
intros.
Admitted.

 *)







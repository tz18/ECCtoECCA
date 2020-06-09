Require Export ECCA_equiv.
Require Import ECCA_reduction_lemmas.
Require Import Equivalence.

Lemma equiv_refl (g: ECCAenv): Reflexive (ECCA_Equiv g).
Proof.
unfold Reflexive. intros.
apply aE_Equiv with (e:= x); auto.
Qed.

Lemma equiv_sym (g: ECCAenv): Symmetric (ECCA_Equiv g).
Proof.
unfold Symmetric. intros. inversion H.
- apply aE_Equiv with (e := e); auto.
- subst. apply aE_EquivIta2 with (x:=x0) (e2:=x) (e1':=e2')(e1:=y)(A:= A)(e:=e).
  + auto.
  + apply H0.
  + apply H2. 
- subst. eapply aE_EquivIta1.
  + apply H1.
  + apply H0.
  + apply H2.
- subst. eapply aE_Reflect. destruct H0.
  + apply or_intror. apply h.
  + apply or_introl. apply h.
Qed.

Lemma equiv_trans (g: ECCAenv): Transitive (ECCA_Equiv g).
Proof.
unfold Transitive. intros. induction H; induction H0; subst.
- cut (exists d, (g |- e =r> d) /\ (g |- e0 =r> d))%ECCA.
  + intros. destruct H3. destruct H3. apply aE_Equiv with (e:=x).
    * apply R_Trans with (e':=e); auto.
    * apply R_Trans with (e':=e0); auto.
  + apply church_rosser with (e:=e2); auto.
- cut (exists d, (g |- e =r> d) /\ (g |- (eAbs A e2) =r> d))%ECCA.
  + intros. destruct H4. destruct H4.
(*need more church rosser stuff for the eta-equivalence cases.*)
Admitted.

(* need to prove that substitution (bind?) respects equivalence, ie if e1 \equiv e2 then B[x:=e] \equiv B[x:=e2]*)
Lemma if_eta_1 (g: ECCAenv) (x: name) (v m1 m2 m: ECCAexp):
  (ECCA_Equiv g (eIf v m1 m2) m) ->
  (ECCA_Equiv (ctx_cons g x (Eq v eTru)) m1 m).
Admitted.

Lemma if_eta_2 (g: ECCAenv) (x: name) (v m1 m2 m: ECCAexp):
  (ECCA_Equiv g (eIf v m1 m2) m) ->
  (ECCA_Equiv (ctx_cons g x (Eq v eFls)) m2 m).
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







Require Export equiv.
Require Import reduction_lemmas.
Require Import Equivalence.

Lemma equiv_refl (g: env): Reflexive (Equiv g).
Proof.
unfold Reflexive. intros.
apply aE_RedCong with (e:= x); auto.
Qed.

Lemma equiv_sym (g: env): Symmetric (Equiv g).
Proof.
unfold Symmetric. intros. inversion H.
- apply aE_RedCong with (e := e); auto.
- subst. apply aE_RedCongIta2 with (x:=x0) (e2:=x) (e1':=e2')(e1:=y)(A:= A)(e:=e).
  + auto.
  + apply H0.
  + apply H2. 
- subst. eapply aE_RedCongIta1.
  + apply H1.
  + apply H0.
  + apply H2.
- subst. eapply aE_Reflect. apply or_comm. apply H0.
Qed.

Lemma equiv_trans (g: env): Transitive (Equiv g).
Proof.
unfold Transitive. intros. induction H; induction H0; subst.
- cut (exists d, (g |- e =r> d) /\ (g |- e0 =r> d))%ECCA.
  + intros. destruct H3. destruct H3. apply aE_RedCong with (e:=x).
    * apply R_Trans with (e':=e); auto.
    * apply R_Trans with (e':=e0); auto.
  + apply church_rosser with (e:=e2); auto.
- cut (exists d, (g |- e =r> d) /\ (g |- (eAbs A e2) =r> d))%ECCA.
  + intros. destruct H4. destruct H4.
(*need more church rosser stuff for the eta-equivalence cases.*)
Admitted.

Lemma equiv_weakening (g: env) (x: name) (a: ctxmem) (e1 e2: exp):
  (Equiv g e1 e2) ->
  (Equiv (ctx_cons g x a) e1 e2).
Admitted.

Lemma if_cong_v_equiv (g: env) (v v' m1 m2: exp):
  (Equiv g v v') ->
  (Equiv g (eIf v m1 m2) (eIf v' m1 m2)).
Proof.
  intros. inversion H. 1,2,3: eapply aE_RedCong.
  - apply R_CongIf. apply H0. apply R_Refl. apply R_Refl.
  - apply R_CongIf. apply H1. apply R_Refl. apply R_Refl.
  - apply R_CongIf. apply H0. apply R_Refl. apply R_Refl.
  - apply R_CongIf. admit. apply R_Refl. apply R_Refl.
  - apply R_CongIf. apply H0. apply R_Refl. apply R_Refl.
  - apply R_CongIf. admit. apply R_Refl. apply R_Refl.
  - admit.
Admitted.

Lemma if_eta_1 (g: env) (x: name) (v m1 m2 m: exp):
  (Equiv g (eIf v m1 m2) m) ->
  (Equiv (ctx_cons g x (Eq v eTru)) m1 m).
Proof.
  intros.
  cut (Equiv (ctx_cons g x (Eq v eTru)) (eIf v m1 m2) (eIf eTru m1 m2)).
  - intros.
    cut (Equiv (ctx_cons g x (Eq v eTru)) (eIf eTru m1 m2) m1).
    + intros. apply equiv_weakening with (x:=x) (a:=Eq v eTru) in H.
      eapply equiv_trans. apply equiv_sym in H1. apply H1.
      eapply equiv_trans. apply equiv_sym in H0. apply H0.
      assumption.
    + apply aE_RedCong with (e:=m1).
      * apply R_RedR. auto.
      * apply R_Refl.
  - cut (Equiv (ctx_cons g x (Eq v eTru)) v eTru).
    + intros. apply if_cong_v_equiv. assumption.
    + apply aE_Reflect with (x:=(free x)). left. apply ctx_has.
Qed.

Lemma if_eta_2 (g: env) (x: name) (v m1 m2 m: exp):
  (Equiv g (eIf v m1 m2) m) ->
  (Equiv (ctx_cons g x (Eq v eFls)) m2 m).
Proof.
  intros.
  cut (Equiv (ctx_cons g x (Eq v eFls)) (eIf v m1 m2) (eIf eFls m1 m2)).
  - intros.
    cut (Equiv (ctx_cons g x (Eq v eFls)) (eIf eFls m1 m2) m2).
    + intros. apply equiv_weakening with (x:=x) (a:=Eq v eFls) in H.
      eapply equiv_trans. apply equiv_sym in H1. apply H1.
      eapply equiv_trans. apply equiv_sym in H0. apply H0.
      assumption.
    + apply aE_RedCong with (e:=m2).
      * apply R_RedR. auto.
      * apply R_Refl.
  - cut (Equiv (ctx_cons g x (Eq v eFls)) v eFls).
    + intros. apply if_cong_v_equiv. assumption.
    + apply aE_Reflect with (x:=(free x)). left. apply ctx_has.
Qed.

Instance Equiv_equiv (g: env) : Equivalence (Equiv g).
Proof.
split. apply equiv_refl. apply equiv_sym. apply equiv_trans.
Qed.
Hint Resolve Equiv_equiv.
Require Import String.

(*TODO: To use this, we need to declare some functions proper wrt to equiv.
Then we can do rewriting. 
See page 17 of 
https://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf *)

(* Require Import typing. *)

(* 
Lemma equiv_distributes_over_pi (g: env) (x: atom) (B B' A A': exp):
(g |- A =e= A' ->
g |- B =e= B' ->
g |- ePi x A B =e= ePi x A' B')%ECCA.
Proof.
intros. inversion H. inversion H0.
- subst.

Lemma equiv_equivariant_over_subst (g: env) (x: atom) (N N' A B: exp):
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
    * eapply aE_RedCong with (e := e); auto.
    * destruct (x == x0).
      ++




  + destruct (x == x0).
    * apply H1.
    * auto.
  + destruct (x == x0).
    * auto. Reset IHB2. inversion IHB1. 
        --

   
- *)
(* Lemma equiv_abs_compositional_1 (g: env) (A A' b: exp): 
(Equiv g A A') ->
(Equiv g (eAbs A b) (eAbs A' b))%ECCA.
Proof.
intros. inversion H.
+ subst. apply aE_RedCong with (e:=eAbs e b); eapply R_CongLam1; auto.
Admitted.

Lemma equiv_abs_compositional_2 (g: env) (x: atom) (A b b': exp): 
(Equiv (Assum g x A) b b') ->
(Equiv g (eAbs x A b) (eAbs x A b'))%ECCA.
Proof.
intros. induction H.
+ apply aE_RedCong with (e:=eAbs x A e); apply R_CongLam1; auto.
Admitted.

Lemma equiv_abs_compositional (g: env) (x: atom) (A A' b b': exp): 
(Equiv g A A') ->
(Equiv (Assum g x A) b b') ->
(Equiv g (eAbs x A b) (eAbs x A' b'))%ECCA.
Proof.
intros.
Admitted.

 *)







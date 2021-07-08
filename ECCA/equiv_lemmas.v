Require Export equiv.
Require Import reduction_lemmas.
Require Import Equivalence.

Lemma equiv_refl (g: env): Reflexive (Equiv g).
Proof.
unfold Reflexive. intros. eapply aE_Reflex. 
Qed.

Lemma equiv_sym (g: env): Symmetric (Equiv g).
Proof.
  unfold Symmetric. intros. eapply aE_Symm. auto.
Qed.

Lemma equiv_trans (g: env): Transitive (Equiv g).
Proof.
  unfold Transitive. intros. eapply aE_Trans. apply H. auto.
Qed.

Instance Equiv_equiv (g: env) : Equivalence (Equiv g).
Proof.
split. apply equiv_refl. apply equiv_sym. apply equiv_trans.
Qed.
Hint Rewrite Equiv_equiv.
Require Import String.



(*TODO: To use this, we need to declare some functions proper wrt to equiv.
Then we can do rewriting. 
See page 17 of 
https://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf *)


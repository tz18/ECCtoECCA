Require Import ECC.
Require Import ECCA_core ECCA_typing ECCA_equiv ECCA_continuations.
Require Import translator.
Require Import ECCA_het_comp.
Require Import ECCA_key_lemmas.

Definition P1 (g : ECCenv) (e A : ECCexp) (h : ECC_has_type g e A) := (
(forall
(g': ECCAenv) (K: cont_r)
(B N: ECCAexp),
ECCA_cont_has_type (appendEnv (transEnv g) g') (unrestrict_cont K) (Cont N (flattenECCAconf (trans A)) B) ->
ECCA_Equiv (appendEnv (transEnv g) g') (flattenECCAconf (trans e)) N ->
ECCA_has_type (appendEnv (transEnv g) g') (flattenECCAconf (transWork (ECC.FV e) e K)) B)).

Definition P2 (g : ECCenv) (h : ECC_Env_WF g) := ECCA_Env_WF (transEnv g).

Combined Scheme ECC_type_env_comb from ECC_env_type_mut, ECC_type_env_mut.

Lemma strong_trans_preservation :

(forall (g : ECCenv) (h : ECC_Env_WF g),  ECCA_Env_WF (transEnv g)) /\
(forall (g : ECCenv) (e A : ECCexp) (H : ECC_has_type g e A),
forall (g': ECCAenv) (K: cont_r)
(B N: ECCAexp),
ECCA_cont_has_type (appendEnv (transEnv g) g') (unrestrict_cont K) (Cont N (flattenECCAconf (trans A)) B) ->
ECCA_Equiv (appendEnv (transEnv g) g') (flattenECCAconf (trans e)) N ->
ECCA_has_type (appendEnv (transEnv g) g') (flattenECCAconf (transWork (ECC.FV e) e K)) B).
Proof.
intros.
simple apply ECC_type_env_comb; intros.
- unfold transWork. simpl.  destruct (atom_fresh empty). destruct (atom_fresh (add x empty)). destruct (atom_fresh (add x0 (add x empty))).
  cut (ECCA_has_type (transEnv g) (Uni uProp) (Uni (uType 0))).
  + shelve. eapply Cut. ...
  + auto.
-
-
Qed.
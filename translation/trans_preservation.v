Require Import ECC.
Require Import ECCA.core ECCA.typing ECCA.equiv ECCA.continuations.
Require Import translator.
Require Import ECCA.key_lemmas.
(* 
Definition P1 (g : ECC.env) (e A : ECC.exp) (h : ECC.Types g e A) :=
  forall (g': ECCA.core.env) (K: cont_r) (B N: ECCA.core.exp),
    ECCA_cont_has_type (appendEnv (transEnv g) g') (unrestrict_cont K) (Cont N (flattenECCAconf (trans A)) B) ->
    ECCA_Equiv (appendEnv (transEnv g) g') (flattenECCAconf (trans e)) N ->
    ECCA.typing.Types (appendEnv (transEnv g) g') (unrestrict_conf (transWork (ECC.FV e) e K)) B.

Definition P2 (g : ECCenv) (h : ECC_Env_WF g) := ECCA_Env_WF (transEnv g).

Lemma strong_trans_preservation :
  (forall (g : ECCenv) (h : ECC_Env_WF g),  ECCA_Env_WF (transEnv g))
  /\
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
  + shelve. (*eapply Cut. *)
  + auto.
Admitted.
 *)
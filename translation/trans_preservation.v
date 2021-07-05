Require Import ECC.
Require Import ECCA.core ECCA.typing ECCA.equiv ECCA.continuations.
Require Import translator.
From Equations Require Import Equations.
(* Require Import ECCA.key_lemmas. *)


Definition P1 (g : ECC.env) (e A : ECC.exp) (h : ECC.Types g e A) :=
forall (g' : env) (K : cont),
cont_is_ANF K ->
forall B N : exp,
(append (translateEnv g) g' ⊩ K : (〔 N : [[A]] 〕 ⇒ B))%ECCA ->
(append (translateEnv g) g' ⊢ [[e]] ≡ N)%ECCA ->
(append (translateEnv g) g' ⊢ translate e K : B)%ECCA.

Definition P2 (g : ECC.env) (h : ECC.WellFormed g) := (⊢ translateEnv g)%ECCA.

Lemma strong_trans_preservation :
(forall g : ECC.env, (⊢ g)%ECC -> (⊢ translateEnv g)%ECCA) 
/\
(forall (g : ECC.env) (e A : ECC.exp),
  (g ⊢ e : A)%ECC ->
  forall (g' : env) (K : cont),
    cont_is_ANF K ->
    forall B N : exp,
      (append (translateEnv g) g' ⊩ K : (〔 N : [[A]] 〕 ⇒ B))%ECCA ->
      (append (translateEnv g) g' ⊢ [[e]] ≡ N)%ECCA ->
      (append (translateEnv g) g' ⊢ translate e K : B)%ECCA).
Proof. 
intros.
simple apply ECC.type_env_comb; intros.
+ simp translate. 
(* - simp translate. destruct (atom_fresh empty). destruct (atom_fresh (add x empty)). destruct (atom_fresh (add x0 (add x empty))).
  cut (ECCA_has_type (transEnv g) (Uni uProp) (Uni (uType 0))).
  + shelve. (*eapply Cut. *)
  + auto. *)
Admitted.

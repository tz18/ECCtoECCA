Require Import ECC.
Require Import ECCA_core ECCA_typing ECCA_equiv ECCA_continuations.
Require Import translator.
Require Import ECCA_het_comp.

Locate ECCAcont.

(* Lemma 1.1 *)
Lemma strong_trans_preservation 
(g: ECCenv) (e A: ECCexp) 
(g': ECCAenv) (K: cont_r) 
(B N: ECCAexp):

(ECC_Env_WF g -> ECCA_Env_WF (transEnv g))
/\
(ECC_has_type g e A ->
ECCA_cont_has_type (appendEnv (transEnv g) g') (unrestrict_cont K) (Cont N (flattenECCAconf (trans A)) B) ->
ECCA_Equiv (appendEnv (transEnv g) g') (flattenECCAconf (trans e)) N ->
ECCA_has_type (appendEnv (transEnv g) g') (flattenECCAconf (het_compose K (trans e) )) B). 
Proof.
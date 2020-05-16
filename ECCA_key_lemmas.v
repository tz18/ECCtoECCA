Require Export ECCA_typing.
Require Export ECCA_equiv_lemmas.
Require Export ECCA_subst_lemmas.
Require Export ECCA_continuations.

Lemma Cut (g: ECCAenv) (K : cont) (N: ECCAexp) (A B B': ECCAexp):
(ECCA_cont_has_type g K (Cont N A B) ->
ECCA_has_type g N A ->
exists B', ECCA_has_type g (fill_hole N K) B' /\ (B' =a= B))%ECCA.
Proof. 
intros. inversion H ; subst ; cbv.
- exists B. split.
  + eauto.
  + eauto.
- exists (subst y N B). split.
  + eapply aT_Let with (n:= N) (m:= M) (A:=A) (B:=B) (x:=y) (g:=g).
    * assumption.
    * assumption.
  + apply subst_no_fv_aeq. auto.
Qed.

Lemma equivalence_is_equivalence (g: ECCAenv) (y: atom) (N N' M: ECCAexp) (A B: ECCAexp):
((g |- N : A) ->
(g |- N' : A) ->
ECCA_Equiv g N N' ->

(((g, y = N), y : A) |- M : B) ->
(((g, y = N'), y : A) |- M : B))%ECCA.
Proof. (* intros. induction H2; default_simp.
1: {shelve. } (* need to show that lookuptype is at most one to one *)
6: {eapply aT_Let. 
    - apply IHECCA_has_type1. 
    - } *)
Abort.

(* Admitting for now. Need a nicer way to formulate well formedness
and/or the idea that a certain id does not already exist in the g *)

Fixpoint domain_of_env (g: ECCAenv): atoms :=
match g with
| Empty => empty 
| Assum g x A => (add x (domain_of_env g))
| Def g x A => (add x (domain_of_env g))
| Eq g e1 e2 => domain_of_env g
end.

Lemma weakening (g : ECCAenv) (x : atom) (N A A' : ECCAexp):
  ECCA_has_type g N A ->
  (* x `notin` (domain_of_env g) -> *)
  ECCA_has_type (Assum g x A') N A.
Admitted.

Lemma def_weakening (g : ECCAenv) (x : atom) (N N' A A' : ECCAexp):
  ECCA_has_type g N A ->
  (* x `notin` (domain_of_env g) -> *)
  ECCA_has_type (Assum (Def g x N') x A') N A.
Admitted.
Require Import Coq.Program.Equality.


(* Dependent induction works for the first case, but not for the other cases. 
Normal induction works for the other cases, but not the first case *)

Lemma equivalence_in_derivation1 (g: ECCAenv) (N N' M : ECCAexp) (A B : ECCAexp) (x : atom):
ECCA_has_type g N A ->
ECCA_has_type g N' A ->
ECCA_Equiv g N N' ->
ECCA_has_type (Assum (Def g x N) x A) M B ->
ECCA_has_type (Assum (Def g x N') x A) M B.
Proof.
  intros. induction H2; auto.
  -  shelve. (* apply aT_Var. inversion H2. 
    + auto. shelve.
    + default_simp.  *)
 (* where is g0 coming from??? *)
  - apply aT_Sig.
    + assumption.
    + apply weakening. assumption.
(*   - shelve. (* apply aT_Prod_Prop with (i := i).
    + assumption.
    + apply weakening. assumption. *)
  - shelve. (*  apply aT_Prod_Type with (i := i).
    + assumption.
    + apply weakening. assumption. *)
  - apply aT_Lam. apply weakening. assumption.
  - apply aT_Let with (A := A0).
    + assumption.
    + apply def_weakening. assumption.
  - apply aT_Conv with (A := A0) (U := U).
    + assumption.
    + assumption.
    + shelve. (* again, where is g0 coming from??? *)
  - apply aT_App with (A':= A'); assumption.
  - apply aT_Fst with (B := B) (x := x0). assumption.
  - apply aT_Snd with (A := A0). *)
Admitted.

Lemma equivalence_in_derivation2 (g: ECCAenv) (N N' M : ECCAexp) (A B : ECCAexp) (x : atom):
ECCA_has_type g N A ->
ECCA_has_type g N' A ->
ECCA_Equiv g N N' ->
ECCA_has_type (Assum (Def g x N) x A) M B ->
ECCA_has_type (Assum (Def g x N') x A) M B.
Proof.
  intros. dependent induction H2; auto.
  - apply aT_Var. inversion H2.
    + auto.
    + default_simp. 
 (* where is g0 coming from??? *)
  - apply aT_Sig.
    + apply IHECCA_has_type1 with (N0:=N); auto.
    + apply weakening. apply IHECCA_has_type2 with (N0:=N'); auto. shelve.
(*   - shelve. (* apply aT_Prod_Prop with (i := i).
    + assumption.
    + apply weakening. assumption. *)
  - shelve. (*  apply aT_Prod_Type with (i := i).
    + assumption.
    + apply weakening. assumption. *)
  - apply aT_Lam. apply weakening. assumption.
  - apply aT_Let with (A := A0).
    + assumption.
    + apply def_weakening. assumption.
  - apply aT_Conv with (A := A0) (U := U).
    + assumption.
    + assumption.
    + shelve. (* again, where is g0 coming from??? *)
  - apply aT_App with (A':= A'); assumption.
  - apply aT_Fst with (B := B) (x := x0). assumption.
  - apply aT_Snd with (A := A0). *)
Admitted.
     
  
Lemma Cut_modulo_equivalence (g: ECCAenv) (K : cont) (N N': ECCAexp) (A B B': ECCAexp):
(ECCA_cont_has_type g K (Cont N A B) ->
ECCA_has_type g N A ->
ECCA_has_type g N' A ->
ECCA_Equiv g N N' ->
exists B', ECCA_has_type g (fill_hole N' K) B' /\ (B' =a= B))%ECCA.
Proof. 
intros. inversion H ; subst ; cbv.
- exists B. split.
  + eauto.
  + eauto.
- exists (subst y N' B). split.
  + eapply aT_Let with (n:= N') (m:= M) (A:=A) (B:=B) (x:=y) (g:=g).
    * assumption.
    * apply equivalence_in_derivation1 with (N := N); assumption.
  + apply subst_no_fv_aeq. auto.
Qed. 



(* | aT_Conv (g: ECCAenv) (e A B U: ECCAexp) :
  (g |- e : A) ->
  (g |- B : U) ->
  (ECCA_sub_type g A B) ->
  (g |- e : B)
       
Unable to unify "(g |- eLet y N M : subst y N B)%ECCA" with "(g |- eLet y N M : B)%ECCA".
 *)


(* 
Goal ECCA_has_type Empty (Fst (Pair Tru Fls 
    (Sig X Bool 
          (If X Bool (Pi Y Bool Bool))))) Bool.
Proof.
eapply aT_Fst with (A:= Bool). eapply aT_Pair.
  - apply aT_True.
  - cbv. apply aT_Conv with (A := Bool) (U := (Uni (uType 0))).
    + apply aT_False.
    + eapply aT_Conv.
      * apply aT_If with (e:= Tru) (e1:= Bool) (e2:= (P 1 : Bool -> Bool)%ECCA) (x:= 20) (B:= (Uni (uType 0))) (U:= Uni (uType 1)). 
        -- apply aT_Ax_Type.
        -- auto.
        -- auto.
        -- cbv. eapply aT_Prod_Type.
          ++ auto.
          ++ auto.
      * apply aT_Ax_Type.
      * cbn. apply aST_Cong. apply aE_EquivAlpha. apply aeq_id.
    + apply aST_Cong. apply aE_Equiv with (e:= eBool).
      * auto.
      * eauto.
Qed. *)

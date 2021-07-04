Require Export typing.

(* Open Scope ECCA_scope.
Theorem weakening {Γ e A}:
  (Γ |- e : A) ->
  forall r Δ,
    Γ =[r]=> Δ ->
    (Δ |- ([r] e) : A).
Proof.
Admitted. *)

Lemma type_well_typed (g: env) (N: exp) (A: exp) :
  Types g N A ->
  WellFormed g ->
  exists U , Types g A U.
Proof.
  induction 1.
  - exists (eUni (uType 1)). apply aT_Ax_Type. auto.
  - exists (eUni (uType (S (S i)))). apply aT_Ax_Type. auto.
  - intros. induction H0.
    + subst. destruct H; destruct h. 
    + subst. destruct H. cbn in h. destruct (bindv (closev x0 x)).
      * names.  
  - exists (eUni (uType 1)). apply aT_Ax_Type. auto.
  - exists (eUni (uType 0)). apply aT_Bool. auto.
  - exists (eUni (uType 0)). apply aT_Bool. auto.
  - apply IHTypes1.
  - exists (eUni (uType 0)). eapply aT_Sig. shelve. shelve.
  - exists (eUni (uType 0)). apply aT_Ax_Prop. shelve.
  - exists (eUni (uType (S i))). apply aT_Ax_Type. shelve.
  - exists (eUni (uProp)). eapply aT_Prod_Prop. shelve. shelve.
  - shelve.
  - shelve.
  - exists U. auto.
  - shelve.
  - shelve.
  - shelve. 
Admitted. 

Lemma has_type_wf_g (g: env) (N: exp) (A: exp) (x : name):
  Types g N A ->
  WellFormed g ->
  WellFormed (g & x ~ (Def N A)).
Proof.
  intros.  apply type_well_typed in H as H1. destruct H1.
  apply wf_Def with (U := x0); auto.
Qed. 
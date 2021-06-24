Require Export typing.

Open Scope ECCA_scope.
Theorem weakening {Γ e A}:
  (Γ |- e : A) ->
  forall r Δ,
    Γ =[r]=> Δ ->
    (Δ |- ([r] e) : A).
Proof.
Admitted.

Open Scope ECCA.
Theorem backwards_reasoning_bool (g:env) (v: exp):
((g |- v : eBool) ->
((g |- v =r> eTru) \/ 
(g |- v =r> eFls))).
Proof.
intros.
inversion H; subst.
+ inversion H0. (* With an id in the context, all we have is the type *)
Abort.

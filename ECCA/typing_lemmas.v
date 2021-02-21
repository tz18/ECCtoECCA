Require Export typing.

Open Scope ECCA_scope.
Theorem weakening {Γ e A}:
  (Γ |- e : A) ->
  forall r Δ,
    Γ =[r]=> Δ ->
    (Δ |- ([r] e) : A).
Proof.
Admitted.

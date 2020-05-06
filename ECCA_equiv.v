Require Export ECCA_reduction.

Reserved Notation "A '=a=' B"  (at level 50).
Inductive ECCA_Aeq : ECCAexp -> ECCAexp -> Prop :=
  | aeq_id (e: ECCAexp):
    e =a= e
  | aeq_var (x: atom):
     (eId x) =a= (eId x)
  | aeq_abs_same (x: atom) (t1 t2 b1 b2: ECCAexp):
     t1 =a= t2 -> 
     b1 =a= b2 ->
     (eAbs x t1 b1) =a= (eAbs x t2 b2)
  | aeq_abs_diff (x y: atom) (t1 t2 b1 b2: ECCAexp):
(*      x <> y -> *)
     x `notin` (FV b2) ->
     b1 =a= (swap y x b2) ->
     t1 =a= t2 ->
     (eAbs x t1 b1) =a= (eAbs y t2 b2)
  | aeq_pi_same (x: atom) (t1 t2 b1 b2: ECCAexp):
     t1 =a= t2 -> 
     b1 =a= b2 ->
     (ePi x t1 b1) =a= (ePi x t2 b2)
  | aeq_pi_diff (x y: atom) (t1 t2 b1 b2: ECCAexp):
(*      x <> y ->  Don't think we need this. If x binds nothing, then our new var could be x.*)
     x `notin` (FV b2) ->
     b1 =a= (swap y x b2) ->
     t1 =a= t2 ->
     (ePi x t1 b1) =a= (ePi y t2 b2)
  | aeq_let_same (x: atom) (t1 t2 b1 b2: ECCAexp):
     t1 =a= t2 -> 
     b1 =a= b2 ->
     (eLet x t1 b1) =a= (eLet x t2 b2)
  | aeq_let_diff (x y: atom) (t1 t2 b1 b2: ECCAexp):
(*      x <> y -> *)
     x `notin` (FV b2) ->
     b1 =a= (swap y x b2) ->
     t1 =a= t2 ->
     (eLet x t1 b1) =a= (eLet y t2 b2)
  | aeq_sig_same (x: atom) (t1 t2 b1 b2: ECCAexp):
     t1 =a= t2 -> 
     b1 =a= b2 ->
     (eSig x t1 b1) =a= (eSig x t2 b2)
  | aeq_sig_diff (x y: atom) (t1 t2 b1 b2: ECCAexp):
(*      x <> y -> *)
     x `notin` (FV b2) ->
     b1 =a= (swap y x b2) ->
     t1 =a= t2 ->
     (eSig x t1 b1) =a= (eSig y t2 b2)
  | aeq_app (t1 t2 t1' t2': ECCAexp):
     t1 =a= t1' ->
     t2 =a= t2' ->
     (eApp t1 t2) =a= (eApp t1' t2')
  | aeq_pair (t1 t2 t1' t2' A A': ECCAexp):
     t1 =a= t1' ->
     t2 =a= t2' ->
     A  =a= A' ->
     (ePair t1 t2 A) =a= (ePair t1' t2' A')
  | aeq_Fst (e e': ECCAexp):
     e =a= e' ->
     (eFst e) =a= (eFst e')
  | aeq_Snd (e e': ECCAexp):
     e =a= e' ->
     (eSnd e) =a= (eSnd e')
(*   | aeq_if (e1 e2 e3 e1' e2' e3': ECCAexp):
     ECCA_Aeq e1 e1' ->
     ECCA_Aeq e2 e2' ->
     ECCA_Aeq e3 e3' ->
     ECCA_Aeq (eIf e1 e2 e3) (eIf e1' e2' e3')*)
where "A '=a=' B"  := (ECCA_Aeq A B): ECCA_scope.
Bind Scope ECCA_scope with ECCA_Aeq.
Hint Constructors ECCA_Aeq.


Reserved Notation "g '|-' A '=e=' B"  (at level 250, A at level 99).
Inductive ECCA_Equiv: ECCAenv -> ECCAexp -> ECCAexp -> Prop :=
  | aE_Equiv (g: ECCAenv) (e e1 e2: ECCAexp) :
      ECCA_RedClosR g e1 e ->
      ECCA_RedClosR g e2 e ->
      ECCA_Equiv g e1 e2
   | aE_EquivIta1 (g: ECCAenv) (e1 A e e2 e2': ECCAexp) (e2': ECCAexp) (x: atom) :
      ECCA_RedClosR g e1 (eAbs x A e) ->
      ECCA_RedClosR g e2 e2' ->
(*       conf_to_val e2' = Some v2' -> *)
      ECCA_Equiv (Assum g x A) e (eApp e2' (eId x)) ->
      ECCA_Equiv g e1 e2 
   | aE_EquivIta2 (g: ECCAenv) (e e1 e1' e2 A : ECCAexp) (e1': ECCAexp) (x: atom) :
      ECCA_RedClosR g e1 e1' ->
      ECCA_RedClosR g e2 (eAbs x A e) ->
(*       conf_to_val e1' = Some v1' -> *)
      ECCA_Equiv (Assum g x A) e (eApp e1' (eId x)) -> (* changed order here *)
      ECCA_Equiv g e1 e2 
  | aE_EquivAlpha (g: ECCAenv) (e1 e2: ECCAexp):
      ECCA_Aeq e1 e2 ->
      ECCA_Equiv g e1 e2
(*   | aE_Subst1 (g: ECCAenv) (e e1 e2 v: ECCAexp) (e': ECCAexp):
(*       conf_to_val e = Some v -> *)
      ECCA_Equiv g e e' ->
      ECCA_Equiv g (eSubst e1 e2 v) e'
  | aE_Subst2 (g: ECCAenv) (e1 e2 v: ECCAexp) (e e': ECCAexp):
(*       conf_to_val e = Some v -> *)
      ECCA_Equiv g e e' ->
      ECCA_Equiv g e' (eSubst e1 e2 v) *)
where "g '|-' A '=e=' B"  := (ECCA_Equiv g A B): ECCA_scope.
(*TODO: rewrite with notation for legibility*)
Bind Scope ECCA_scope with ECCA_Equiv.
Hint Constructors ECCA_Equiv.
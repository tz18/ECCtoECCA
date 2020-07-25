Require Export reduction.

Reserved Notation "g '|-' A '=e=' B"  (at level 250, A at level 99).
Inductive Equiv: env -> exp -> exp -> Prop :=
  | aE_RedCong (g: env) (e e1 e2: exp) :
      RedClos g e1 e ->
      RedClos g e2 e ->
      Equiv g e1 e2
   | aE_RedCongIta1 (g: env) (e1 A e e2 e2': exp) (x: name) :
      RedClos g e1 (eAbs A e) ->
      RedClos g e2 e2' ->
(*       conf_to_val e2' = Some v2' -> *)
      Equiv (ctx_cons g x (Assum A)) (open x e) (eApp e2' (eId (free x))) ->
      Equiv g e1 e2 
   | aE_RedCongIta2 (g: env) (e e1 e1' e2 A : exp) (x: name) :
      RedClos g e1 e1' ->
      RedClos g e2 (eAbs A e) ->
(*       conf_to_val e1' = Some v1' -> *)
      Equiv (ctx_cons g x (Assum A)) (open x e) (eApp e1' (eId (free x))) -> (* changed order here *)
      Equiv g e1 e2
   | aE_Reflect (g : env) (x : atom) (e1 e2 : exp):
       (has g x (Eq e1 e2)) \/ (has g x (Eq e2 e1)) ->
       Equiv g e1 e2
(*   | aE_RedCongAlpha (g: env) (e1 e2: exp):
      ECCA_Aeq e1 e2 ->
      Equiv g e1 e2 *)
(*   | aE_Subst1 (g: env) (e e1 e2 v: exp) (e': exp):
(*       conf_to_val e = Some v -> *)
      Equiv g e e' ->
      Equiv g (eSubst e1 e2 v) e'
  | aE_Subst2 (g: env) (e1 e2 v: exp) (e e': exp):
(*       conf_to_val e = Some v -> *)
      Equiv g e e' ->
      Equiv g e' (eSubst e1 e2 v) *)
where "g '|-' A '=e=' B"  := (Equiv g A B): ECCA_scope.
(*TODO: rewrite with notation for legibility*)
Bind Scope ECCA_scope with Equiv.
Hint Constructors Equiv.

(* 
Reserved Notation "A '=a=' B"  (at level 50).
Inductive ECCA_Aeq : exp -> exp -> Prop :=
  | aeq_id (e: exp):
    e =a= e
  | aeq_var (x: atom):
     (eId x) =a= (eId x)
  | aeq_abs_same (x: atom) (t1 t2 b1 b2: exp):
     t1 =a= t2 -> 
     b1 =a= b2 ->
     (eAbs x t1 b1) =a= (eAbs x t2 b2)
  | aeq_abs_diff (x y: atom) (t1 t2 b1 b2: exp):
(*      x <> y -> *)
     x `notin` (FV b2) ->
     b1 =a= (swap y x b2) ->
     t1 =a= t2 ->
     (eAbs x t1 b1) =a= (eAbs y t2 b2)
  | aeq_pi_same (x: atom) (t1 t2 b1 b2: exp):
     t1 =a= t2 -> 
     b1 =a= b2 ->
     (ePi x t1 b1) =a= (ePi x t2 b2)
  | aeq_pi_diff (x y: atom) (t1 t2 b1 b2: exp):
(*      x <> y ->  Don't think we need this. If x binds nothing, then our new var could be x.*)
     x `notin` (FV b2) ->
     b1 =a= (swap y x b2) ->
     t1 =a= t2 ->
     (ePi x t1 b1) =a= (ePi y t2 b2)
  | aeq_let_same (x: atom) (t1 t2 b1 b2: exp):
     t1 =a= t2 -> 
     b1 =a= b2 ->
     (eLet x t1 b1) =a= (eLet x t2 b2)
  | aeq_let_diff (x y: atom) (t1 t2 b1 b2: exp):
(*      x <> y -> *)
     x `notin` (FV b2) ->
     b1 =a= (swap y x b2) ->
     t1 =a= t2 ->
     (eLet x t1 b1) =a= (eLet y t2 b2)
  | aeq_sig_same (x: atom) (t1 t2 b1 b2: exp):
     t1 =a= t2 -> 
     b1 =a= b2 ->
     (eSig x t1 b1) =a= (eSig x t2 b2)
  | aeq_sig_diff (x y: atom) (t1 t2 b1 b2: exp):
(*      x <> y -> *)
     x `notin` (FV b2) ->
     b1 =a= (swap y x b2) ->
     t1 =a= t2 ->
     (eSig x t1 b1) =a= (eSig y t2 b2)
  | aeq_app (t1 t2 t1' t2': exp):
     t1 =a= t1' ->
     t2 =a= t2' ->
     (eApp t1 t2) =a= (eApp t1' t2')
  | aeq_pair (t1 t2 t1' t2' A A': exp):
     t1 =a= t1' ->
     t2 =a= t2' ->
     A  =a= A' ->
     (ePair t1 t2 A) =a= (ePair t1' t2' A')
  | aeq_Fst (e e': exp):
     e =a= e' ->
     (eFst e) =a= (eFst e')
  | aeq_Snd (e e': exp):
     e =a= e' ->
     (eSnd e) =a= (eSnd e')
(*   | aeq_if (e1 e2 e3 e1' e2' e3': exp):
     ECCA_Aeq e1 e1' ->
     ECCA_Aeq e2 e2' ->
     ECCA_Aeq e3 e3' ->
     ECCA_Aeq (eIf e1 e2 e3) (eIf e1' e2' e3')*)
where "A '=a=' B"  := (ECCA_Aeq A B): ECCA_scope.
Bind Scope ECCA_scope with ECCA_Aeq.
Hint Constructors ECCA_Aeq.
 *)

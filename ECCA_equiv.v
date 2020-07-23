Require Export ECCA_reduction.

Reserved Notation "g '|-' A '=e=' B"  (at level 250, A at level 99).
Inductive ECCA_Equiv: ECCAenv -> ECCAexp -> ECCAexp -> Prop :=
  | aE_Step (g: ECCAenv) (e e1 e2: ECCAexp) :
    ECCA_RedClosR g e1 e ->
    ECCA_RedClosR g e2 e ->
    ECCA_Equiv g e1 e2
  | aE_Reflect (g : ECCAenv) (e1 e2 : ECCAexp) (x: name):
    (has g x (Eq e1 e2)) -> (* stuff in the context needs a name even though eq shoudln't *)
    ECCA_Equiv g e1 e2
  | aE_Subst (g: ECCAenv) (M M1 M2: ECCAexp):
    ECCA_Equiv g M1 M2 ->
    ECCA_Equiv g (bind M1 M) (bind M2 M)
  | aE_Refl (g: ECCAenv) (M: ECCAexp):
    ECCA_Equiv g M M
  | aE_Symm (g: ECCAenv) (M M': ECCAexp):
    ECCA_Equiv g M' M ->
    ECCA_Equiv g M M'
  | aE_Trans (g: ECCAenv) (M1 M2 M': ECCAexp):
    ECCA_Equiv g M1 M' ->
    ECCA_Equiv g M' M2 ->
    ECCA_Equiv g M1 M2
  | aE_Lam (g: ECCAenv) (A A' M M': ECCAexp) (x: name):
    ECCA_Equiv g A A' ->
    ECCA_Equiv (g ~ (Assum x A)) (open x M) (open x M') ->
    ECCA_Equiv (eAbs A M) (eAbs A' M')
  | aE_Eta1 (g: ECCAenv) (A M M1 M2 M': ECCAexp) (x: name):
    ECCA_Equiv g M1 (eAbs A M) ->
    ECCA_Equiv g M2 M' ->
    ECCA_Equiv (g ~ (Assum x A)) (open x M) (eApp M' (eId x)) ->
    ECCA_Equiv g M1 M2
  | aE_Eta2 (g: ECCAenv) (A M M1 M2 M': ECCAexp) (x: name):
    ECCA_Equiv g M1 M' ->
    ECCA_Equiv g M2 (eAbs A M)
    ECCA_Equiv (g ~ (Assum x A)) (open x M) (eApp M' (eId x)) ->
    ECCA_Equiv g M1 M2
  | aE_App (g: ECCAenv) (V1 V1' V2 V2': ECCAexp): 
    ECCA_Equiv g V1 V1' ->
    ECCA_Equiv g V2 V2' ->
    ECCA_Equiv g (eApp V1 V2) (eApp V1' V2')
  | aE_Pi (g: ECCAenv) (A A' B B': ECCAexp) (x: name):
    ECCA_Equiv g A A' ->
    ECCA_Equiv (g ~ (Assum x A)) (open x B) (open x B') ->
    ECCA_Equiv g (ePi A B) (ePi A' B')
  | aE_Pair (g: ECCAenv) (V1 V1' V2 V2' A A': ECCAexp):
    ECCA_Equiv g V1 V1' ->
    ECCA_Equiv g V2 V2' ->
    ECCA_Equiv g A A' ->
    ECCA_Equiv g (ePair V1 V2 A) (ePair V1' V2' A')
  | aE_Fst (g: ECCAenv) (V V': ECCAexp):
    ECCA_Equiv g V V' ->
    ECCA_Equiv g (eFst V) (eFst V')
  | aE_Snd (g: ECCAenv) (V V': ECCAexp):
    ECCA_Equiv g V V'
    ECCA_Equiv g (eSnd V) (eSnd V')
  | aE_Sig (g: ECCAenv) (A A' B B': ECCAexp) (x: name):
    ECCA_Equiv g A A' ->
    ECCA_Equiv (g ~ (Assum x A)) B B' ->
    ECCA_Equiv g (eSig A B) (eSig A' B')
  | aE_Let (g: ECCAenv) (N N' M M' A: ECCAexp) (x: name):
    ECCA_Equiv g N N' -> (* uh oh *)
    ECCA_Equiv (g ~ (Def x N A)) (open x M) (open X M') ->
    ECCA_Equiv g (eLet N M) (eLet N' M')
  | aE_If (g: ECCAenv) (V V' M1 M1' M2 M2': ECCAexp):
    ECCA_Equiv g V V' ->
    ECCA_Equiv g M1 M1' ->
    ECCA_Equiv g M2 M2' ->
    ECCA_Equiv g (eIf V M1 M2) (eIf V' M1' M2')
  | aE_If_EtaTru (g: ECCAenv) (V M1 M2: ECCAexp) (x: name):
    (has g x (Eq V true)) ->
    ECCA_Equiv g (eIf V M1 M2) M1
  | aE_IfEtaFls (g: ECCAenv) (V M1 M2: ECCAexp) (x: name):
    (has g x (Eq V fls)) ->
    ECCA_Equiv g (eIf V M1 M2) M2
where "g '|-' A '=e=' B"  := (ECCA_Equiv g A B): ECCA_scope.
(*TODO: rewrite with notation for legibility*)
Bind Scope ECCA_scope with ECCA_Equiv.
Hint Constructors ECCA_Equiv.

(*   | aE_EquivIta1 (g: ECCAenv) (e1 A e e2 e2': ECCAexp) (x: name) :
      ECCA_RedClosR g e1 (eAbs A e) ->
      ECCA_RedClosR g e2 e2' ->
(*       conf_to_val e2' = Some v2' -> *)
      ECCA_Equiv (ctx_cons g x (Assum A)) (open x e) (eApp e2' (eId (free x))) ->
      ECCA_Equiv g e1 e2 
  | aE_EquivIta2 (g: ECCAenv) (e e1 e1' e2 A : ECCAexp) (x: name) :
      ECCA_RedClosR g e1 e1' ->
      ECCA_RedClosR g e2 (eAbs A e) ->
(*       conf_to_val e1' = Some v1' -> *)
      ECCA_Equiv (ctx_cons g x (Assum A)) (open x e) (eApp e1' (eId (free x))) -> (* changed order here *)
      ECCA_Equiv g e1 e2 *)

(* 
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
 *)

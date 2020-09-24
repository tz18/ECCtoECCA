Require Export reduction.

Reserved Notation "g '|-' A '=e=' B"  (at level 250, A at level 99).
Inductive Equiv: env -> exp -> exp -> Prop :=
  | aE_Step (g: env) (e e1 e2: exp) :
    RedClos g e1 e ->
    RedClos g e2 e ->
    Equiv g e1 e2
  | aE_Reflect (g : env) (e1 e2 : exp) (x: var):
    (has g x (Eq e1 e2)) -> (* stuff in the context needs a name even though eq shoudln't *)
    Equiv g e1 e2
  | aE_Subst (g: env) (M M1 M2: exp):
    Equiv g M1 M2 ->
    Equiv g (bind M1 M) (bind M2 M)
  | aE_Refl (g: env) (M: exp):
    Equiv g M M
  | aE_Symm (g: env) (M M': exp):
    Equiv g M' M ->
    Equiv g M M'
  | aE_Trans (g: env) (M1 M2 M': exp):
    Equiv g M1 M' ->
    Equiv g M' M2 ->
    Equiv g M1 M2
  | aE_Lam (g: env) (A A' M M': exp) (x: name):
    Equiv g A A' ->
    Equiv (g & x ~ (Assum A)) (open x M) (open x M') ->
    Equiv g (eAbs A M) (eAbs A' M')
  | aE_Eta1 (g: env) (A M M1 M2 M': exp) (x: name):
    Equiv g M1 (eAbs A M) ->
    Equiv g M2 M' ->
    Equiv (g & x ~ (Assum A)) (open x M) (eApp M' (eId (free x))) ->
    Equiv g M1 M2
  | aE_Eta2 (g: env) (A M M1 M2 M': exp) (x: name):
    Equiv g M1 M' ->
    Equiv g M2 (eAbs A M) ->
    Equiv (g & x ~ (Assum A)) (open x M) (eApp M' (eId (free x))) ->
    Equiv g M1 M2
  | aE_App (g: env) (V1 V1' V2 V2': exp): 
    Equiv g V1 V1' ->
    Equiv g V2 V2' ->
    Equiv g (eApp V1 V2) (eApp V1' V2')
  | aE_Pi (g: env) (A A' B B': exp) (x: name):
    Equiv g A A' ->
    Equiv (g & x ~ (Assum A)) (open x B) (open x B') ->
    Equiv g (ePi A B) (ePi A' B')
  | aE_Pair (g: env) (V1 V1' V2 V2' A A': exp):
    Equiv g V1 V1' ->
    Equiv g V2 V2' ->
    Equiv g A A' ->
    Equiv g (ePair V1 V2 A) (ePair V1' V2' A')
  | aE_Fst (g: env) (V V': exp):
    Equiv g V V' ->
    Equiv g (eFst V) (eFst V')
  | aE_Snd (g: env) (V V': exp):
    Equiv g V V' ->
    Equiv g (eSnd V) (eSnd V')
  | aE_Sig (g: env) (A A' B B': exp) (x: name):
    Equiv g A A' ->
    Equiv (g & x ~ (Assum A)) (open x B) (open x B') ->
    Equiv g (eSig A B) (eSig A' B')
  | aE_Let (g: env) (N N' M M' A: exp) (x: name):
    Equiv g N N' -> (* uh oh *)
    Equiv (g & x ~ (Def N A)) (open x M) (open x M') ->
    Equiv g (eLet N M) (eLet N' M')
  | aE_If (g: env) (V V' M1 M1' M2 M2': exp) (x: name):
    Equiv g V V' ->
    Equiv (g & x ~ (Eq V eTru)) M1 M1' ->
    Equiv (g & x ~ (Eq V eFls)) M2 M2' ->
    Equiv g (eIf V M1 M2) (eIf V' M1' M2')
  | aE_If_EtaTru (g: env) (V M1 M2: exp) (x: var):
    (has g x (Eq V eTru)) ->
    Equiv g (eIf V M1 M2) M1
  | aE_IfEtaFls (g: env) (V M1 M2: exp) (x: var):
    (has g x (Eq V eFls)) ->
    Equiv g (eIf V M1 M2) M2
  | aE_If2 (g: env) (V M: exp):
    Equiv g (eIf V M M) M
where "g '|-' A '=e=' B"  := (Equiv g A B): ECCA_scope.
(*TODO: rewrite with notation for legibility*)
Bind Scope ECCA_scope with Equiv.
Hint Constructors Equiv.
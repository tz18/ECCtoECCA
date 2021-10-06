Require Export reduction.


Reserved Notation "g '⊢' A '≡' B"  (at level 250, A at level 99). (*⊢ : \vdash , ≡ : \equiv *) 
Inductive Equiv : env -> exp -> exp -> Prop :=
  | aE_Step (g : env) (e e' : exp):
      (g ⊢ e ⊳ e') ->  
      (g ⊢ e ≡ e')
  | aE_Reflect : forall (g : env) (e1 e2 : exp) (x : var),
      assumes g x (eEqv e1 e2) -> 
      (g ⊢ e1 ≡ e2)
  | aE_Subst : forall (g : env) (M M1 M2 : exp),
      (g ⊢ M1 ≡ M2) -> 
      (g ⊢ bind M1 M ≡ bind M2 M)
  | aE_Reflex : forall (g : env) (M : exp), 
      (g ⊢ M ≡ M)
  | aE_Symm : forall (g : env) (M M' : exp), 
      (g ⊢ M' ≡ M) ->
      (g ⊢ M ≡ M')
  | aE_Trans : forall (g : env) (M1 M2 M' : exp),
      (g ⊢ M1 ≡ M') -> 
      (g ⊢ M' ≡ M2) -> 
      (g ⊢ M1 ≡ M2)
  | aE_Lam : forall (g : env) (A A' M M' : exp) (x : name),
      (g ⊢ A ≡ A') ->
      (g & x ~ Assum A ⊢ open x M ≡ open x M') ->
      (g ⊢ eAbs A M ≡ eAbs A' M')
  | aE_Eta (g : env) (A F' F G G' : exp) (x : name): (* I think this is wrong *)
      (g ⊢ F ≡ eAbs A F') ->
      (g ⊢ G ≡ G') ->
      (g & x ~ Assum A ⊢ open x F' ≡ eApp ([^x] G') (eId (free x))) -> 
      (g ⊢ F ≡ G)
  | aE_App : forall (g : env) (V1 V1' V2 V2' : exp),
      (g ⊢ V1 ≡ V1') -> 
      (g ⊢ V2 ≡ V2') -> 
      (g ⊢ eApp V1 V2 ≡ eApp V1' V2')
  | aE_Pi : forall (g : env) (A A' B B' : exp) (x : name),
      (g ⊢ A ≡ A') ->
      (g & x ~ Assum A ⊢ open x B ≡ open x B') -> 
      (g ⊢ ePi A B ≡ ePi A' B')
  | aE_Pair : forall (g : env) (V1 V1' V2 V2' A A' : exp),
      (g ⊢ V1 ≡ V1') ->
      (g ⊢ V2 ≡ V2') -> 
      (g ⊢ A ≡ A') -> 
      (g ⊢ ePair V1 V2 A ≡ ePair V1' V2' A')
  | aE_Fst : forall (g : env) (V V' : exp), 
      (g ⊢ V ≡ V') -> 
      (g ⊢ eFst V ≡ eFst V')
  | aE_Snd : forall (g : env) (V V' : exp), 
      (g ⊢ V ≡ V') -> 
      (g ⊢ eSnd V ≡ eSnd V')
  | aE_Sig : forall (g : env) (A A' B B' : exp) (x : name),
      (g ⊢ A ≡ A') ->
      (g & x ~ Assum A ⊢ open x B ≡ open x B') -> 
      (g ⊢ eSig A B ≡ eSig A' B')
  | aE_Let : forall (g : env) (N N' M M' A : exp) (x : name),
      (g ⊢ N ≡ N') ->
      (g & x ~ Def N A ⊢ open x M ≡ open x M') -> 
      (g ⊢ eLet N M ≡ eLet N' M')
  | aE_If : forall (g : env) (V V' M1 M1' M2 M2' : exp) (p : name),
      (g ⊢ V ≡ V') ->
      (g & p ~ Assum (eEqv V eTru) ⊢ [^p] M1 ≡ [^p] M1') ->
      (g & p ~ Assum (eEqv V eFls) ⊢ [^p] M2 ≡ [^p] M2') -> 
      (g ⊢ eIf V M1 M2 ≡ eIf V' M1' M2')
  | aE_If_EtaTru : forall (g : env) (V M1 M2 : exp) (p : var),
      assumes g p (eEqv V eTru) -> 
      (g ⊢ eIf V M1 M2 ≡ M1)
  | aE_If_EtaFls : forall (g : env) (V M1 M2 : exp) (p : var),
      assumes g p (eEqv V eFls) -> 
      (g ⊢ eIf V M1 M2 ≡ M2)
  | aE_If2 : forall (g : env) (V M : exp), 
      (g ⊢ eIf V M M ≡ M)
where "g '⊢' A '≡' B"  := (Equiv g A B): ECCA_scope.
Bind Scope ECCA_scope with Equiv.
Hint Constructors Equiv.
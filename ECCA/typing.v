Require Export equiv.
(*
================================
=======--Type System--==========
================================
*)

Reserved Notation "g '⊢' A '≲' B"  (at level 250, A at level 99). (*⊢ : \vdash , ≲ : \less *) 
Inductive SubTypes: env -> exp -> exp -> Prop :=
  | ST_Cong : forall (g : env) (A B : exp), 
    (g ⊢ A ≡ B) -> 
    (g ⊢ A ≲ B)
  | ST_Cum : forall (g : env) (i : nat), 
    (g ⊢ eUni (uType i) ≲ eUni (uType (S i)))
  | ST_Pi : forall (g : env) (A1 A2 B1 B2 : exp) (x : name),
    (g ⊢ A1 ≡ A2) ->
    (g & x ~ Assum A2 ⊢ open x B1 ≲ open x B2) ->
    (g ⊢ ePi A1 B1 ≲ ePi A2 B2)
  | ST_Trans : forall (g : env) (A A' B : exp),
    (g ⊢ A ≲ A') -> 
    (g ⊢ A' ≲ B) -> (g ⊢ A ≲ B)
  | ST_Prop : forall g : env, 
    (g ⊢ eUni uProp ≲ eUni (uType 0))
  | ST_Sig : forall (g : env) (A1 A2 B1 B2 : exp) (x : name),
    (g ⊢ A1 ≲ A2) ->
    (g & x ~ Assum A2 ⊢ open x B1 ≲ open x B2) ->
    (g ⊢ eSig A1 B1 ≲ eSig A2 B2)
where "g '⊢' a '≲' b" := (SubTypes g a b) : ECCA_scope.

Print SubTypes.
Hint Constructors SubTypes.

Reserved Notation "g '⊢' a ':' b" (at level 250, a at level 99).
Reserved Notation "'⊢' g" (at level 250).
Inductive Types: env -> exp -> exp -> Prop :=
| aT_Ax_Prop (g: env) :
  WellFormed g ->
  (g ⊢ (eUni uProp) : (eUni (uType 0)))
| aT_Ax_Type (g: env) (i: nat) :
  WellFormed g ->
  (g ⊢ (eUni (uType i)) : (eUni (uType (S i))))
| aT_Var (g: env) (x: atom) (A: exp) :
  (⊢ g) -> 
  (assumes g x A) -> (* this needs adjustment *)
  (g ⊢ (eId x) : A)
| aT_Bool (g: env):
  WellFormed g ->
  (g ⊢ (eBool) : (eUni (uType 0)))
| aT_True (g: env):
  WellFormed g ->
  (g ⊢ (eTru) : (eBool))
| aT_False (g: env):
  WellFormed g ->
  (g ⊢ (eFls) : (eBool)) 
| aT_Sig (g: env) (x: name) (A B: exp) (i: nat) :
  (g ⊢ A : (eUni (uType i))) ->
  ((g & x ~ Assum A) ⊢ (open x B): (eUni (uType i))) ->
  (g ⊢ (eSig A B) : (eUni (uType i)))
| aT_Pair (g: env) (v1 v2: exp) (A B: exp) :
  (g ⊢ v1 : A) ->
  (g ⊢ v2 : (bind v1 B)) ->
  (g ⊢ (ePair v1 v2 (eSig A B)) : (eSig A B))
| aT_Prod_Prop (g: env) (x: name) (A B: exp) (i: nat):
  (g ⊢ A : (eUni (uType i))) ->
  (Types (g & x ~ Assum A) (open x B) (eUni (uProp))) ->
  (g ⊢ (ePi A B) : (eUni (uProp)))
| aT_Prod_Type (g: env) (x: name) (A B: exp) (i: nat):
  (g ⊢ A : (eUni (uType i))) ->
  (Types (g & x ~ Assum A) (open x B) (eUni (uType i))) ->
  (g ⊢ (ePi A B) : (eUni (uType i)))
| aT_Lam (g: env) (x: name) (A e B: exp) :
  (Types (g & x ~ Assum A) (open x e) (open x B)) ->
  (g ⊢ (eAbs A e) : (ePi A B))
| aT_Let (g: env) (n m A B: exp) (x: name):
  (g ⊢ n : A) ->
  (Types (g & x ~ Def n A) (open x m) (open x B)) ->
  (g ⊢ (eLet n m) : (bind n B))
| aT_If (g: env) (B U e1 e2: exp) (e: exp) (x p: name):
  ((g & x ~ Assum eBool) ⊢ (open x B): U) -> 
  (g ⊢ e : eBool) ->
  ((g & p ~ (Assum (eEqv e eTru))) ⊢ [^p] e1 : (bind eTru ([^p] B))) ->
  ((g & p ~ (Assum (eEqv e eFls))) ⊢ [^p] e2 : (bind eFls ([^p] B))) -> 
  (g ⊢ (eIf e e1 e2) : (bind e B)) 
| aT_Conv (g: env) (e A B U: exp) :
  (g ⊢ e : A) ->
  (g ⊢ B : U) ->
  (SubTypes g A B) ->
  (g ⊢ e : B)
| aT_App (g: env) (e e': exp) (A' B: exp) :
  (g ⊢ e : (ePi A' B)) ->
  (g ⊢ e' : A') ->
  (g ⊢ (eApp e e') : (bind e B))
| aT_Fst (g: env) (e: exp) (A B: exp) :
  (g ⊢ e: (eSig A B)) ->
  (g ⊢ (eFst e): A)
| aT_Snd (g: env) (e: exp) (A B: exp) :
  (g ⊢ e: (eSig A B)) ->
  (g ⊢ (eSnd e): (bind (eFst e) B)) 
| aT_Refl (g: env) (e: exp) (A: exp):
  (g ⊢ e: A) ->
  (g ⊢ (eRefl e): (eEqv e e)) 
| aT_Equiv (g: env) (A A': exp) (i: nat):
  (g ⊢ A: (eUni (uType i))) ->
  (g ⊢ A': (eUni (uType i))) ->
  (g ⊢ (eEqv A A'): (eUni (uType i)))
where "g '⊢' a ':' b" := (Types g a b) : ECCA_scope
with (* ECCA Well-Formed Environments *)
WellFormed: env -> Prop :=
  | wf_Empty : 
    (⊢ ctx_empty)
  | wf_Assum : forall (g : env) (x : name) (A U : exp),
    (⊢ g) -> 
    (g ⊢ A : U) -> 
    (⊢ g & x ~ Assum A)
  | wf_Def : forall (g : env) (x : name) (e A U : exp),
    (⊢ g) -> 
    (g ⊢ A : U) -> 
    (g ⊢ e : A) -> 
    (⊢ g & x ~ Def e A)
where "'⊢' g" := (WellFormed g) : ECCA_scope.
Hint Constructors Types.
Hint Constructors WellFormed.

Scheme Types_WellFormed_ind := Induction for Types Sort Prop
  with WellFormed_Types_ind := Induction for WellFormed Sort Prop.

Combined Scheme Types_WellFormed_mutind from Types_WellFormed_ind, WellFormed_Types_ind.
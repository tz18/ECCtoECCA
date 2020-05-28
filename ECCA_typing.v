Require Export ECCA_equiv.

(*
================================
=======--Type System--==========
================================
*)

(* TODO: Add notation for subtypes. *)
Inductive ECCA_sub_type: ECCAenv -> ECCAexp -> ECCAexp -> Prop :=
| aST_Cong (g: ECCAenv) (A B: ECCAexp) :
  ECCA_Equiv g A B ->
  ECCA_sub_type g A B
| aST_Cum (g: ECCAenv) (i: nat) :
  ECCA_sub_type g (eUni (uType i)) (eUni (uType (S i)))
| aST_Pi (g: ECCAenv) (A1 A2 B1 B2: ECCAexp) (x: name) :
  (ECCA_Equiv g A1 A2) ->
  (ECCA_sub_type (g & x ~ Assum A2) (open x B1) (open x B2)) -> (* eId x1 ?*)
  (ECCA_sub_type g (ePi A1 B1) (ePi A2 B2))
| aST_Trans (g: ECCAenv) (A A' B: ECCAexp) :
  (ECCA_sub_type g A A') ->
  (ECCA_sub_type g A' B) ->
  (ECCA_sub_type g A B)
| aST_Prop (g: ECCAenv) :
  (ECCA_sub_type g (eUni (uProp)) (eUni (uType 0)))
| aST_Sig (g: ECCAenv) (A1 A2 B1 B2: ECCAexp) (x: name):
  (ECCA_sub_type g A1 A2) ->
  (ECCA_sub_type (g & x ~ Assum A2) (open x B1) (open x B2)) ->
  (ECCA_sub_type g (eSig A1 B1) (eSig A2 B2))
.
Hint Constructors ECCA_sub_type.

Reserved Notation "g '|-' a ':' b" (at level 250, a at level 99).
Inductive ECCA_has_type: ECCAenv -> ECCAexp -> ECCAexp -> Prop :=
| aT_Ax_Prop (g: ECCAenv) :
  ECCA_Env_WF g ->
  (g |- (eUni uProp) : (eUni (uType 0)))
| aT_Ax_Type (g: ECCAenv) (i: nat) :
  ECCA_Env_WF g ->
  (g |- (eUni (uType i)) : (eUni (uType (S i))))
| aT_Var (g: ECCAenv) (x: atom) (A: ECCAexp) :
  (assumes g x A) -> (* this needs adjustment *)
  (g |- (eId x) : A)
| aT_Bool (g: ECCAenv):
  ECCA_Env_WF g ->
  (g |- (eBool) : (eUni (uType 0)))
| aT_True (g: ECCAenv):
  ECCA_Env_WF g ->
  (g |- (eTru) : (eBool))
| aT_False (g: ECCAenv):
  ECCA_Env_WF g ->
  (g |- (eFls) : (eBool)) 
| aT_Sig (g: ECCAenv) (x: name) (A B: ECCAexp) (i: nat) :
  (g |- A : (eUni (uType i))) ->
  (ECCA_has_type (g & x ~ Assum A) (open x B) (eUni (uType i))) ->
  (g |- (eSig A B) : (eUni (uType i)))
| aT_Pair (g: ECCAenv) (v1 v2: ECCAexp) (A B: ECCAexp) :
  (g |- v1 : A) ->
  (g |- v2 : (bind v1 B)) ->
  (g |- (ePair v1 v2 (eSig A B)) : (eSig A B))
| aT_Prod_Prop (g: ECCAenv) (x: name) (A B: ECCAexp) (i: nat):
  (g |- A : (eUni (uType i))) ->
  (ECCA_has_type (g & x ~ Assum A) (open x B) (eUni (uProp))) ->
  (g |- (ePi A B) : (eUni (uProp)))
| aT_Prod_Type (g: ECCAenv) (x: name) (A B: ECCAexp) (i: nat):
  (g |- A : (eUni (uType i))) ->
  (ECCA_has_type (g & x ~ Assum A) (open x B) (eUni (uType i))) ->
  (g |- (ePi A B) : (eUni (uType i)))
| aT_Lam (g: ECCAenv) (x: name) (A e B: ECCAexp) :
  (ECCA_has_type (g & x ~ Assum A) (open x e) (open x B)) ->
  (g |- (eAbs A e) : (ePi A B))
(* ECCA_has_type: ECCAenv -> ECCAconf -> ECCAconf -> Prop := *)
| aT_Let (g: ECCAenv) (n m A B: ECCAexp) (x: name):
  (g |- n : A) ->
(*should this be (def(assum(g))) or (assum(def(g)))*)
  (ECCA_has_type (g & x ~ Def n A) (open x m) (open x B)) ->
  (g |- (eLet n m) : (bind n B))
(* | aT_If (g: ECCAenv) (B U e1 e2: ECCAexp) (e: ECCAexp) (x: atom):
  ECCA_has_type (Assum g x eBool) B U -> 
  g |- e : eBool ->
  ECCA_has_type (Eq g e eTru) e1 (subst x eTru B) ->
  ECCA_has_type (Eq g e eFls) e2 (subst x eFls B) -> 
  g |- (eIf e e1 e2) : (subst x e B) *)
| aT_Conv (g: ECCAenv) (e A B U: ECCAexp) :
  (g |- e : A) ->
  (g |- B : U) ->
  (ECCA_sub_type g A B) ->
  (g |- e : B)
(* ECCA_has_type: ECCAenv -> ECCAcomp -> ECCAconf -> Prop := *)
| aT_App (g: ECCAenv) (x: name) (e e': ECCAexp) (A' B: ECCAexp) :
  (g |- e : (ePi A' B)) ->
  (g |- e' : A') ->
  (g |- (eApp e e') : (bind e B))
| aT_Fst (g: ECCAenv) (e: ECCAexp) (A B: ECCAexp) :
  (g |- e: (eSig A B)) ->
  (g |- (eFst e): A)
| aT_Snd (g: ECCAenv) (e: ECCAexp) (A B: ECCAexp) :
  (g |- e: (eSig A B)) ->
  (g |- (eSnd e): (bind (eFst e) B)) 
(* | aT_Subst (x: atom) (g: ECCAenv) (A B U: ECCAexp) (e e1 e2: ECCAexp):
  (ECCA_has_type (Assum g x A) B U) ->
  g |- e1: A -> 
  g |- e2: A ->
  g |- e: (subst x e1 B) ->
  ECCA_LookupEqR g e1 e2 ->
  g |- (eSubst e1 e2 e): (subst x e2 B)  *)
where "g '|-' a ':' b" := (ECCA_has_type g a b) : ECCA_scope
with 
(* ECCA Well-Formed Environments *)
ECCA_Env_WF: ECCAenv -> Prop :=
| W_Empty (g: ECCAenv) :
  ECCA_Env_WF ctx_empty
| W_Assum (g: ECCAenv) (x: name) (A U: ECCAexp) :
  ECCA_Env_WF g ->
  ECCA_has_type g A U ->
  ECCA_Env_WF (g & x ~ Assum A)
| W_Def (g: ECCAenv) (x: name) (e A U: ECCAexp) :
  ECCA_Env_WF g ->
  ECCA_has_type g A U ->
  ECCA_has_type g e A ->
  ECCA_Env_WF (g & x ~ Def e A)
(* | W_Eq  *)
.
Hint Constructors ECCA_has_type.
Hint Constructors ECCA_Env_WF.
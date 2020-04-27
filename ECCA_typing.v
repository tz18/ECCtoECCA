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
| aST_Pi (g: ECCAenv) (A1 A2 B1 B2: ECCAexp) (x1 x2: atom) :
  (ECCA_Equiv g A1 A2) ->
  (ECCA_sub_type (Assum g x1 A2) B1 (subst x2 (eId x1) B2)) -> (* eId x1 ?*)
  (ECCA_sub_type g (ePi x1 A1 B1) (ePi x2 A2 B2))
.
Hint Constructors ECCA_sub_type.

Reserved Notation "g '|-' a ':' b" (at level 50, a at level 99).
Inductive ECCA_has_type: ECCAenv -> ECCAexp -> ECCAexp -> Prop :=
| aT_Ax_Prop (g: ECCAenv) :
  (g |- (eUni uProp) : (eUni (uType 0)))
| aT_Ax_Type (g: ECCAenv) (i: nat) :
  (g |- (eUni (uType i)) : (eUni (uType (S i))))
| aT_Var (g: ECCAenv) (x: atom) (A: ECCAexp) :
  (ECCA_LookupTypeR g x A) -> (* this needs adjustment *)
  (g |- (eId x) : A)
| aT_Bool (g: ECCAenv):
  (g |- (eBool) : (eUni (uType 0)))
| aT_True (g: ECCAenv):
  (g |- (eTru) : (eBool))
| aT_False (g: ECCAenv):
  (g |- (eFls) : (eBool)) 
| aT_Sig (g: ECCAenv) (x: atom) (A B: ECCAexp) (i: nat) :
  (g |- A : (eUni (uType i))) ->
  (ECCA_has_type (Assum g x A) B (eUni (uType i))) ->
  (g |- (eSig x A B) : (eUni (uType i)))
| aT_Pair (g: ECCAenv) (v1 v2: ECCAexp) (A B: ECCAexp) (x: atom) :
  (g |- v1 : A) ->
  (g |- v2 : (subst x v1 B)) ->
  (g |- (ePair v1 v2 (eSig x A B)) : (eSig x A B))
| aT_Prod_Prop (g: ECCAenv) (x: atom) (A B: ECCAexp) (i: nat):
  (g |- A : (eUni (uType i))) ->
  (ECCA_has_type (Assum g x A) B (eUni (uProp))) ->
  (g |- (ePi x A B) : (eUni (uProp)))
| aT_Prod_Type (g: ECCAenv) (x: atom) (A B: ECCAexp) (i: nat):
  (g |- A : (eUni (uType i))) ->
  (ECCA_has_type (Assum g x A) B (eUni (uType i))) ->
  (g |- (ePi x A B) : (eUni (uType i)))
| aT_Lam (g: ECCAenv) (x: atom) (A e B: ECCAexp) :
  (ECCA_has_type (Assum g x A) e B) ->
  (g |- (eAbs x A e) : (ePi x A B))
(* ECCA_has_type: ECCAenv -> ECCAconf -> ECCAconf -> Prop := *)
| aT_Let (g: ECCAenv) (n m A B: ECCAexp) (x: atom):
  (g |- n : A) ->
(*should this be (def(assum(g))) or (assum(def(g)))*)
  (ECCA_has_type (Assum (Def g x n) x A) m B) ->
  (g |- (eLet x n m) : (subst x n B))
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
| aT_App (g: ECCAenv) (x: atom) (e e': ECCAexp) (A' B: ECCAexp) :
  (g |- e : (ePi x A' B)) ->
  (g |- e' : A') ->
  (g |- (eApp e e') : (subst x e B))
| aT_Fst (g: ECCAenv) (e: ECCAexp) (A B: ECCAexp) (x: atom) :
  (g |- e: (eSig x A B)) ->
  (g |- (eFst e): A)
| aT_Snd (g: ECCAenv) (e: ECCAexp) (A B: ECCAexp) (x: atom) :
  (g |- e: (eSig x A B)) ->
  (g |- (eSnd e): (subst x (eFst e) B)) 
(* | aT_Subst (x: atom) (g: ECCAenv) (A B U: ECCAexp) (e e1 e2: ECCAexp):
  (ECCA_has_type (Assum g x A) B U) ->
  g |- e1: A -> 
  g |- e2: A ->
  g |- e: (subst x e1 B) ->
  ECCA_LookupEqR g e1 e2 ->
  g |- (eSubst e1 e2 e): (subst x e2 B)  *)
where "g '|-' a ':' b" := (ECCA_has_type g a b) : ECCA_scope
.
Hint Constructors ECCA_has_type.

(* ECC Well-Formed Environments *)
Inductive ECCA_Env_WF: ECCAenv -> Prop :=
| W_Empty (g: ECCAenv) :
  ECCA_Env_WF Empty
| W_Assum (g: ECCAenv) (x: atom) (A U: ECCAexp) :
  ECCA_Env_WF g ->
  ECCA_has_type g A U ->
  ECCA_Env_WF (Assum g x A)
| W_Def (g: ECCAenv) (x: atom) (e A U: ECCAexp) :
  ECCA_Env_WF g ->
  ECCA_has_type g A U ->
  ECCA_has_type g e A ->
  ECCA_Env_WF (Assum (Def g x e) x A)
.
Hint Constructors ECCA_Env_WF.
Require Export equiv.
Require Export core_lemmas.
(*
================================
=======--Type System--==========
================================
*)

(* TODO: Add notation for subtypes. *)
Inductive SubTypes: env -> exp -> exp -> Prop :=
| aST_Cong (g: env) (A B: exp) :
  Equiv g A B ->
  SubTypes g A B
| aST_Cum (g: env) (i: nat) :
  SubTypes g (eUni (uType i)) (eUni (uType (S i)))
| aST_Pi (g: env) (A1 A2 B1 B2: exp) (x: name) :
  (Equiv g A1 A2) ->
  (SubTypes (g & x ~ Assum A2) (open x B1) (open x B2)) -> (* eId x1 ?*)
  (SubTypes g (ePi A1 B1) (ePi A2 B2))
| aST_Trans (g: env) (A A' B: exp) :
  (SubTypes g A A') ->
  (SubTypes g A' B) ->
  (SubTypes g A B)
| aST_Prop (g: env) :
  (SubTypes g (eUni (uProp)) (eUni (uType 0)))
| aST_Sig (g: env) (A1 A2 B1 B2: exp) (x: name):
  (SubTypes g A1 A2) ->
  (SubTypes (g & x ~ Assum A2) (open x B1) (open x B2)) ->
  (SubTypes g (eSig A1 B1) (eSig A2 B2))
.
Hint Constructors SubTypes.

Reserved Notation "g '|-' a ':' b" (at level 250, a at level 99).
Inductive Types: env -> exp -> exp -> Prop :=
| aT_Ax_Prop (g: env) :
 (*  WellFormed g -> *)
  (g |- (eUni uProp) : (eUni (uType 0)))
| aT_Ax_Type (g: env) (i: nat) :
(*   WellFormed g -> *)
  (g |- (eUni (uType i)) : (eUni (uType (S i))))
| aT_Var (g: env) (x: atom) (A: exp) :
  (assumes g x A) -> (* this needs adjustment *)
  (g |- (eId x) : A)
| aT_Bool (g: env):
(*   WellFormed g -> *)
  (g |- (eBool) : (eUni (uType 0)))
| aT_True (g: env):
(*   WellFormed g -> *)
  (g |- (eTru) : (eBool))
| aT_False (g: env):
(*   WellFormed g -> *)
  (g |- (eFls) : (eBool)) 
| aT_Sig (g: env) (x: name) (A B: exp) (i: nat) :
  (g |- A : (eUni (uType i))) ->
  ((g & x ~ Assum A) |- (open x B): (eUni (uType i))) ->
  (g |- (eSig A B) : (eUni (uType i)))
| aT_Pair (g: env) (v1 v2: exp) (A B: exp) :
  (g |- v1 : A) ->
  (g |- v2 : (bind v1 B)) ->
  (g |- (ePair v1 v2 (eSig A B)) : (eSig A B))
| aT_Prod_Prop (g: env) (x: name) (A B: exp) (i: nat):
  (g |- A : (eUni (uType i))) ->
  (Types (g & x ~ Assum A) (open x B) (eUni (uProp))) ->
  (g |- (ePi A B) : (eUni (uProp)))
| aT_Prod_Type (g: env) (x: name) (A B: exp) (i: nat):
  (g |- A : (eUni (uType i))) ->
  (Types (g & x ~ Assum A) (open x B) (eUni (uType i))) ->
  (g |- (ePi A B) : (eUni (uType i)))
| aT_Lam (g: env) (x: name) (A e B: exp) :
  (Types (g & x ~ Assum A) (open x e) (open x B)) ->
  (g |- (eAbs A e) : (ePi A B))
| aT_Let (g: env) (n m A B: exp) (x: name):
  (g |- n : A) ->
  (Types (g & x ~ Def n A) (open x m) (open x B)) ->
  (g |- (eLet n m) : (bind n B))
| aT_If (g: env) (B U e1 e2: exp) (e: exp) (x y: name):
  ((g & x ~ Assum eBool) |- (open x B): U) -> 
  (g |- e : eBool) ->
  ((g & y ~ Eq e eTru) |- e1 : (bind eTru B)) ->
  ((g & y ~ Eq e eFls) |- e2 : (bind eFls B)) -> 
  (g |- (eIf e e1 e2) : (bind e B)) 
| aT_Conv (g: env) (e A B U: exp) :
  (g |- e : A) ->
  (g |- B : U) ->
  (SubTypes g A B) ->
  (g |- e : B)
| aT_App (g: env) (x: name) (e e': exp) (A' B: exp) :
  (g |- e : (ePi A' B)) ->
  (g |- e' : A') ->
  (g |- (eApp e e') : (bind e B))
| aT_Fst (g: env) (e: exp) (A B: exp) :
  (g |- e: (eSig A B)) ->
  (g |- (eFst e): A)
| aT_Snd (g: env) (e: exp) (A B: exp) :
  (g |- e: (eSig A B)) ->
  (g |- (eSnd e): (bind (eFst e) B)) 
where "g '|-' a ':' b" := (Types g a b) : ECCA_scope
(* with 
(* ECCA Well-Formed Environments *)
WellFormed: env -> Prop :=
| wf_Empty:
  WellFormed ctx_empty
| wf_Assum (g: env) (x: name) (A U: exp) :
  WellFormed g ->
  Types g A U ->
  WellFormed (g & x ~ Assum A)
| wf_Def (g: env) (x: name) (e A U: exp) :
  WellFormed g ->
  Types g A U ->
  Types g e A ->
  WellFormed (g & x ~ Def e A) *)
(* | W_Eq  *)
.

Hint Constructors Types.

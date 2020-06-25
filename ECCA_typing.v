Require Export ECCA_equiv.
Require Export ECCA_core_lemmas.
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
| aT_Let (g: ECCAenv) (n m A B: ECCAexp) (x: name):
  (g |- n : A) ->
  (ECCA_has_type (g & x ~ Def n A) (open x m) (open x B)) ->
  (g |- (eLet n m) : (bind n B))
| aT_If (g: ECCAenv) (B U e1 e2: ECCAexp) (e: ECCAexp) (x y: name):
  ECCA_has_type (g & x ~ Assum eBool) (open x B) U -> 
  ECCA_has_type g e eBool ->
  ECCA_has_type (g & y ~ Eq e eTru) e1 (bind eTru B) ->
  ECCA_has_type (g & y ~ Eq e eFls) e2 (bind eFls B) -> 
  (g |- (eIf e e1 e2) : (bind e B)) 
| aT_Conv (g: ECCAenv) (e A B U: ECCAexp) :
  (g |- e : A) ->
  (g |- B : U) ->
  (ECCA_sub_type g A B) ->
  (g |- e : B)
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
where "g '|-' a ':' b" := (ECCA_has_type g a b) : ECCA_scope
with 
(* ECCA Well-Formed Environments *)
ECCA_Env_WF: ECCAenv -> Prop :=
| W_Empty (g: @ECCAenv 0) :
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

(* 
=====================================
Well boundedness wrt Type Environments 
=====================================
*)

Inductive ECCA_wf {V: nat}: ECCAenv -> ECCAexp -> Prop :=
| wf_Prop (g: ECCAenv) :
    (* ECCA_Env_WF g -> *)
    ECCA_wf g (eUni uProp)
| wf_Type (g: ECCAenv) (i: nat) :
    (* ECCA_Env_WF g -> *)
    ECCA_wf g (eUni (uType i))
| wf_Var (g: ECCAenv) (x: atom) (A: ECCAexp) :
    (assumes g x A) -> (* this needs adjustment *)
    ECCA_wf g (eId x)
| wf_Bool (g: ECCAenv) :
    (* ECCA_Env_WF g -> *)
    ECCA_wf g eBool
| wf_True (g: ECCAenv):
    (* ECCA_Env_WF g -> *)
    ECCA_wf g eTru
| wf_False (g: ECCAenv):
    (* ECCA_Env_WF g -> *)
    ECCA_wf g eFls
| wf_Sig (g: ECCAenv) (x: name) (A B: ECCAexp) (i: nat) :
    ECCA_wf g A ->
    ECCA_wf (g & x ~ Assum A) (open x B) ->
    ECCA_wf g (eSig A B)
| wf_Pair (g: ECCAenv) (v1 v2: ECCAexp) (A B: ECCAexp) (x: name) :
    ECCA_wf g v1 ->
    ECCA_wf g v2 ->
    ECCA_wf g A ->
    ECCA_wf (g & x ~ Def v1 A) (open x B) ->
    ECCA_wf g (ePair v1 v2 (eSig A B))
| wf_Pi (g: ECCAenv) (x: name) (A B: ECCAexp) :
    ECCA_wf g A ->
    ECCA_wf (g & x ~ Assum A) (open x B) ->
    ECCA_wf g (ePi A B)
| wf_Lam (g: ECCAenv) (x: name) (A e B: ECCAexp) :
    ECCA_wf (g & x ~ Assum A) (open x B) ->
    ECCA_wf (g & x ~ Assum A) (open x e) ->
    ECCA_wf g (eAbs A e)
| wf_Let (g: ECCAenv) (n m A: ECCAexp) (x: name):
    ECCA_wf g n ->
    ECCA_wf g A ->
    ECCA_has_type g n A ->
(*     ECCA_wf (g & x ~ Def n A) (open x B) -> *)
    ECCA_wf (g & x ~ Def n A) (open x m) ->
    ECCA_wf g (eLet n m)
| wf_If (g: ECCAenv) (B e1 e2: ECCAexp) (e: ECCAexp) (x y: name):
    ECCA_wf (g & x ~ Assum eBool) (open x B) -> 
    ECCA_wf g e ->
    ECCA_wf (g & y ~ Eq e eTru) e1 ->
    ECCA_wf (g & y ~ Eq e eFls) e2 -> 
    ECCA_wf g (eIf e e1 e2)
| wf_App (g: ECCAenv) (x: name) (e e': ECCAexp):
    ECCA_wf g e ->
    ECCA_wf g e' ->
    ECCA_wf g (eApp e e')
| wf_Fst (g: ECCAenv) (e: ECCAexp) :
    ECCA_wf g e ->
    ECCA_wf g (eFst e)
| wf_Snd (g: ECCAenv) (e: ECCAexp) :
    ECCA_wf g e ->
    ECCA_wf g (eSnd e)
.

(*
Inductive ECCAval {V: nat}: Type :=
  | Id (x: @atom V)
  | Uni (U: ECCuni)
  | Pi (A: ECCAconf) (B: @ECCAconf (S V))
  | Abs (A: ECCAconf) (B: @ECCAconf (S V))
  | Sig (A: ECCAconf) (B: @ECCAconf (S V))
  | Pair (v1 v2: ECCAval) (A: @ECCAconf V)
  | Tru
  | Fls
  | Bool
with
ECCAconf {V: nat}: Type :=
  | Comp (e: ECCAcomp)
  | Let (A: ECCAcomp) (B: @ECCAconf (S V))
  | If (v: ECCAval) (m1 m2: ECCAconf)
with
ECCAcomp {V: nat}: Type :=
  | App (v1 v2: ECCAval)
  | Val (v: ECCAval)
  | Fst (v: ECCAval)
  | Snd (v: ECCAval)
.*)

Inductive ECCA_val_wf {V: nat}: @ECCAenv 0 -> ECCAval -> Prop :=
| wf_val_Id (g: ECCAenv) (A: ECCAexp) (x: atom):
    (assumes g x A) -> (* this needs adjustment *)
    ECCA_val_wf g (Id x)
| wf_val_Prop (g: ECCAenv) :
    ECCA_Env_WF g ->
    ECCA_val_wf g (Uni uProp)
| wf_val_Type (g: ECCAenv) (i: nat) :
    ECCA_Env_WF g ->
    ECCA_val_wf g (Uni (uType i))
| wf_val_Bool (g: ECCAenv) :
    ECCA_Env_WF g ->
    ECCA_val_wf g Bool
| wf_val_True (g: ECCAenv):
    ECCA_Env_WF g ->
    ECCA_val_wf g Tru
| wf_val_False (g: ECCAenv):
    ECCA_Env_WF g ->
    ECCA_val_wf g Fls
| wf_val_Sig (g: ECCAenv) (x: name) (A B: ECCAconf) (i: nat) :
    ECCA_conf_wf g A ->
    ECCA_conf_wf (g & x ~ Assum (flattenECCAconf A)) (open_conf x B) ->
    ECCA_val_wf g (Sig A B)
| wf_val_Pair (g: ECCAenv) (v1 v2: ECCAval) (A B: ECCAconf) (x: name) :
    ECCA_val_wf g v1 ->
    ECCA_val_wf g v2 ->
    ECCA_conf_wf g A ->
    ECCA_conf_wf (g & x ~ Def (flattenECCAval v1) (flattenECCAconf A)) (open_conf x B) ->
    ECCA_val_wf g (Pair v1 v2 (Sig A B))
| wf_val_Pi (g: ECCAenv) (x: name) (A B: ECCAconf) :
    ECCA_conf_wf g A ->
    ECCA_conf_wf (g & x ~ Assum (flattenECCAconf A)) (open_conf x B) ->
    ECCA_val_wf g (Pi A B)
| wf_val_Lam (g: ECCAenv) (x: name) (A e: ECCAconf) :
    ECCA_conf_wf (g & x ~ Assum (flattenECCAconf A)) (open_conf x e) ->
    ECCA_val_wf g (Abs A e)
with ECCA_conf_wf {V: nat}: ECCAenv -> ECCAconf -> Prop :=  
| wf_conf_Comp (g: ECCAenv) (e: ECCAcomp):
    ECCA_comp_wf g e ->
    ECCA_conf_wf g (Comp e)
| wf_conf_Let (g: ECCAenv) (n: ECCAcomp) (m A: ECCAconf) (x: name):
    ECCA_comp_wf g n ->
    ECCA_conf_wf g A ->
    ECCA_conf_wf (g & x ~ Def (flattenECCAcomp n) (flattenECCAconf A)) (open_conf x m) ->
    ECCA_conf_wf g (Let n m)
| wf_conf_If (g: ECCAenv) (v: ECCAval) (B m1 m2: ECCAconf) (x y: name):
    ECCA_conf_wf (g & x ~ Assum eBool) (open_conf x B) -> 
    ECCA_val_wf g v ->
    ECCA_conf_wf (g & y ~ Eq (flattenECCAval v) eTru) m1 ->
    ECCA_conf_wf (g & y ~ Eq (flattenECCAval v) eFls) m2 -> 
    ECCA_conf_wf g (If v m1 m2)
with ECCA_comp_wf {V: nat}: ECCAenv -> ECCAcomp -> Prop :=
| wf_comp_Val (g: ECCAenv) (v: ECCAval):
    ECCA_val_wf g v ->
    ECCA_comp_wf g (Val v)
| wf_comp App (g: ECCAenv) (x: name) (v v': ECCAval):
    ECCA_val_wf g v ->
    ECCA_val_wf g v' ->
    ECCA_comp_wf g (App v v')
| wf_comp_Fst (g: ECCAenv) (v: ECCAval) :
    ECCA_val_wf g v ->
    ECCA_comp_wf g (Fst v)
| wf_comp_Snd (g: ECCAenv) (v: ECCAval) :
    ECCA_val_wf g v ->
    ECCA_comp_wf g (Snd v)
.

Hint Constructors ECCA_has_type.
Hint Constructors ECCA_Env_WF.


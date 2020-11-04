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
  WellFormed g ->
  (g |- (eUni uProp) : (eUni (uType 0)))
| aT_Ax_Type (g: env) (i: nat) :
  WellFormed g ->
  (g |- (eUni (uType i)) : (eUni (uType (S i))))
| aT_Var (g: env) (x: atom) (A: exp) :
  (assumes g x A) -> (* this needs adjustment *)
  (g |- (eId x) : A)
| aT_Bool (g: env):
  WellFormed g ->
  (g |- (eBool) : (eUni (uType 0)))
| aT_True (g: env):
  WellFormed g ->
  (g |- (eTru) : (eBool))
| aT_False (g: env):
  WellFormed g ->
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
with 
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
  WellFormed (g & x ~ Def e A)
(* | W_Eq  *)
.

(* 
=====================================
Well boundedness wrt Type Environments 
=====================================
*)

Inductive WellBound: env -> @exp 0 -> Prop :=
| wb_Prop (g: env) :
    WellFormed g ->
    WellBound g (eUni uProp)
| wb_Type (g: env) (i: nat) :
    WellFormed g ->
    WellBound g (eUni (uType i))
| wb_Var (g: env) (x: atom) (A: exp) :
    (assumes g x A) -> (* this needs adjustment *)
    WellBound g (eId x)
| wb_Bool (g: env) :
    WellFormed g ->
    WellBound g eBool
| wb_True (g: env):
    WellFormed g ->
    WellBound g eTru
| wb_False (g: env):
    WellFormed g ->
    WellBound g eFls
| wb_Sig (g: env) (x: name) (A B: exp) (i: nat) :
    WellBound g A ->
    WellBound (g & x ~ Assum A) (open x B) ->
    WellBound g (eSig A B)
| wb_Pair (g: env) (v1 v2: exp) (A B: exp) (x: name) :
    WellBound g v1 ->
    WellBound g v2 ->
    WellBound g A ->
    WellBound (g & x ~ Def v1 A) (open x B) ->
    WellBound g (ePair v1 v2 (eSig A B))
| wb_Pi (g: env) (x: name) (A B: exp) :
    WellBound g A ->
    WellBound (g & x ~ Assum A) (open x B) ->
    WellBound g (ePi A B)
| wb_Lam (g: env) (x: name) (A e B: exp) :
    WellBound (g & x ~ Assum A) (open x B) ->
    WellBound (g & x ~ Assum A) (open x e) ->
    WellBound g (eAbs A e)
| wb_Let (g: env) (n m A B: exp) (x: name):
    WellBound g n ->
    WellBound g A ->
    WellBound (g & x ~ Def n A) (open x B) ->
    WellBound (g & x ~ Def n A) (open x m) ->
    WellBound g (eLet n m)
| wb_If (g: env) (B e1 e2: exp) (e: exp) (x y: name):
    WellBound (g & x ~ Assum eBool) (open x B) -> 
    WellBound g e ->
    WellBound (g & y ~ Eq e eTru) e1 ->
    WellBound (g & y ~ Eq e eFls) e2 -> 
    WellBound g (eIf e e1 e2)
| wb_App (g: env) (x: name) (e e': exp):
    WellBound g e ->
    WellBound g e' ->
    WellBound g (eApp e e')
| wb_Fst (g: env) (e: exp) :
    WellBound g e ->
    WellBound g (eFst e)
| wb_Snd (g: env) (e: exp) :
    WellBound g e ->
    WellBound g (eSnd e)
.

(*
Inductive val {V: nat}: Type :=
  | Id (x: @atom V)
  | Uni (U: universe)
  | Pi (A: conf) (B: @conf (S V))
  | Abs (A: conf) (B: @conf (S V))
  | Sig (A: conf) (B: @conf (S V))
  | Pair (v1 v2: val) (A: @conf V)
  | Tru
  | Fls
  | Bool
with
conf {V: nat}: Type :=
  | Comp (e: comp)
  | Let (A: comp) (B: @conf (S V))
  | If (v: val) (m1 m2: conf)
with
comp {V: nat}: Type :=
  | App (v1 v2: val)
  | Val (v: val)
  | Fst (v: val)
  | Snd (v: val)
.*)

Inductive WellBound_val: env -> @val 0 -> Prop :=
| wb_val_Id (g: env) (A: exp) (x: atom):
    (assumes g x A) -> (* this needs adjustment *)
    WellBound_val g (Id x)
| wb_val_Prop (g: env) :
    WellFormed g ->
    WellBound_val g (Uni uProp)
| wb_val_Type (g: env) (i: nat) :
    WellFormed g ->
    WellBound_val g (Uni (uType i))
| wb_val_Bool (g: env) :
    WellFormed g ->
    WellBound_val g Bool
| wb_val_True (g: env):
    WellFormed g ->
    WellBound_val g Tru
| wf_val_False (g: env):
    WellFormed g ->
    WellBound_val g Fls
| wf_val_Sig (g: env) (x: name) (A B: conf) (i: nat) :
    WellBound_conf g A ->
    WellBound_conf (g & x ~ Assum (unrestrict_conf A)) (open_conf x B) ->
    WellBound_val g (Sig A B)
| wf_val_Pair (g: env) (v1 v2: val) (A B: conf) (x: name) :
    WellBound_val g v1 ->
    WellBound_val g v2 ->
    WellBound_conf g A ->
    WellBound_conf (g & x ~ Def (unrestrict_val v1) (unrestrict_conf A)) (open_conf x B) ->
    WellBound_val g (Pair v1 v2 (Sig A B))
| wf_val_Pi (g: env) (x: name) (A B: conf) :
    WellBound_conf g A ->
    WellBound_conf (g & x ~ Assum (unrestrict_conf A)) (open_conf x B) ->
    WellBound_val g (Pi A B)
| wf_val_Lam (g: env) (x: name) (A e: conf) :
    WellBound_conf (g & x ~ Assum (unrestrict_conf A)) (open_conf x e) ->
    WellBound_val g (Abs A e)
with WellBound_conf: env -> @conf 0 -> Prop :=  
| wf_conf_Comp (g: env) (e: comp):
    WellBound_comp g e ->
    WellBound_conf g (Comp e)
| wf_conf_Let (g: env) (n: comp) (m A: conf) (x: name):
    WellBound_comp g n ->
    WellBound_conf g A ->
    WellBound_conf (g & x ~ Def (unrestrict_comp n) (unrestrict_conf A)) (open_conf x m) ->
    WellBound_conf g (Let n m)
| wf_conf_If (g: env) (v: val) (B m1 m2: conf) (x y: name):
    WellBound_conf (g & x ~ Assum eBool) (open_conf x B) -> 
    WellBound_val g v ->
    WellBound_conf (g & y ~ Eq (unrestrict_val v) eTru) m1 ->
    WellBound_conf (g & y ~ Eq (unrestrict_val v) eFls) m2 -> 
    WellBound_conf g (If v m1 m2)
with WellBound_comp: env -> @comp 0 -> Prop :=
| wf_comp_Val (g: env) (v: val):
    WellBound_val g v ->
    WellBound_comp g (Val v)
| wf_comp App (g: env) (x: name) (v v': val):
    WellBound_val g v ->
    WellBound_val g v' ->
    WellBound_comp g (App v v')
| wf_comp_Fst (g: env) (v: val) :
    WellBound_val g v ->
    WellBound_comp g (Fst v)
| wf_comp_Snd (g: env) (v: val) :
    WellBound_val g v ->
    WellBound_comp g (Snd v)
.

Hint Constructors Types.
Hint Constructors WellFormed.


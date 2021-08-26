Require Export core.


(*
=====================================
=======--Reduction Relation--========
=====================================
*)

(* -Step- *)
Reserved Notation "g '⊢' e1 '⊳' e2" (at level 250, e1 at level 99). (* ⊢ : \vdash , ⊳ : \RightTriangle *)
Inductive Steps : env -> exp -> exp -> Prop :=
  | st_ID (g: env) (x: atom) (e' A: exp) :
    g ∋ x ~ Def e' A -> (g ⊢ eId x ⊳ e')
  | st_App (g: env) (A body arg: exp) :
    (g ⊢ eApp (eAbs A body) arg ⊳ bind arg body)
  | st_Fst (g: env) (e1 e2 A: exp) :
    (g ⊢ eFst (ePair e1 e2 A) ⊳ e1)
  | st_Snd (g: env) (e1 e2 A: exp) :
    (g ⊢ eSnd (ePair e1 e2 A) ⊳ e2)
  | st_Let (g: env) (e1 e2: exp) :
    (g ⊢ eLet e1 e2 ⊳ bind e1 e2)  
  | st_IfTru (g: env) (e1 e2: exp) :
    (g ⊢ eIf eTru e1 e2 ⊳ e1)
  | st_IfFls (g: env) (e1 e2: exp) :
    (g ⊢ eIf eFls e1 e2 ⊳ e2)
where "g '⊢' e1 '⊳' e2":= (Steps g e1 e2): ECCA_scope.

Hint Constructors Steps.
Bind Scope ECCA_scope with Steps.

(* Congruence Conversion Rules*)
Reserved Notation "g '⊢' e1 '⊳*' e2" (at level 250, e1 at level 99). (* ⊢ : \vdash , ⊳ : \RightTriangle *) 
Inductive Reduces : env -> exp -> exp -> Prop :=
  | R_RedR (g: env) (e e': exp):
      (Steps g e e') ->
      (g ⊢ e ⊳* e')
  | R_Reflex (g: env) (e: exp):
      (g ⊢ e ⊳* e)
  | R_Trans (g: env) (e e' e'': exp) :
      (g ⊢ e ⊳* e') ->
      (g ⊢ e' ⊳* e'') ->
      (g ⊢ e ⊳* e'')
  | R_CongLet (g: env) (e e': exp) (e1 e2 A: exp) (x: name) :
      (g ⊢ e ⊳* e') ->
      ((g & x ~ Def e A) ⊢ (open x e1) ⊳* (open x e2)) -> (*FIXME: where does A come from *)
      (g ⊢ (eLet e e1) ⊳* (eLet e' e2))
  | R_CongLam1 (g: env) (A: exp) (A' e e': exp) (x: name)   :
      (g ⊢ A ⊳* A') ->
      (g & x ~ Assum A ⊢ open x e ⊳* open x e') ->
      (g ⊢ eAbs A e ⊳* eAbs A' e')
  | R_CongPi (g: env) (A: exp) (A' B B': exp) (x: name) :
      (g ⊢ A ⊳* A') ->
      (g & x ~ Assum A ⊢ open x B ⊳* open x B') -> 
      (g ⊢ ePi A B ⊳* ePi A' B')
  | R_CongSig (g: env) (A: exp) (A' B B': exp) (x: name) :
      (g ⊢ A ⊳* A') ->
      (g & x ~ Assum A ⊢ open x B ⊳* open x B') -> 
      (g ⊢ eSig A B ⊳* eSig A' B')
  | R_CongPair (g: env) (e1 e1' e2 e2' A A': exp) :
      (g ⊢ e1 ⊳* e1') ->
      (g ⊢ e2 ⊳* e2') -> 
      (g ⊢ A ⊳* A') -> 
      (g ⊢ ePair e1 e2 A ⊳* ePair e1' e2' A')
  | R_CongApp (g: env) (e1 e1' e2 e2': exp) :
      (g ⊢ e1 ⊳* e1') -> 
      (g ⊢ e2 ⊳* e2') -> 
      (g ⊢ eApp e1 e2 ⊳* eApp e1' e2')
  | R_CongFst (g: env) (V V': exp) :
      (g ⊢ V ⊳* V') -> 
      (g ⊢ eFst V ⊳* eFst V')
  | R_CongSnd (g: env) (V V': exp) :
      (g ⊢ V ⊳* V') -> 
      (g ⊢ eSnd V ⊳* eSnd V')
  | R_CongIf (g: env) (e e' e1 e1' e2 e2': exp) :
      (g ⊢ e ⊳* e') ->
      (g ⊢ e1 ⊳* e1') -> 
      (g ⊢ e2 ⊳* e2') -> 
      (g ⊢ eIf e e1 e2 ⊳* eIf e' e1' e2')
where "g '⊢' e1 '⊳*' e2":= (Reduces g e1 e2): ECCA_scope.

Hint Constructors Reduces.
Bind Scope ECCA_scope with Reduces.

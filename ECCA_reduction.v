Require Export ECCA_subst.


(*
=====================================
=======--Reduction Relation--========
=====================================
*)

(* -Step- *)
Inductive ECCA_RedR : ECCAenv -> ECCAexp -> ECCAexp -> Prop :=
  | R_ID (g: ECCAenv) (x: atom) (e': ECCAexp) :
    ECCA_LookupDefR g x e' -> ECCA_RedR g (eId x) e'
  | R_App (g: ECCAenv) (x: atom) (A body arg: ECCAexp) :
    ECCA_RedR g (eApp (eAbs x A body) arg) (subst x arg body) (*do anything with env here?*)
  | R_Fst (g: ECCAenv) (e1 e2 A: ECCAexp) :
    ECCA_RedR g (eFst (ePair e1 e2 A)) e1
  | R_Snd (g: ECCAenv) (e1 e2 A: ECCAexp) :
    ECCA_RedR g (eSnd (ePair e1 e2 A)) e2
  | R_Let (g: ECCAenv) (x: atom) (e1 e2: ECCAexp) :
    ECCA_RedR g (eLet x e1 e2) (subst x e1 e2)  (*or here?*)
(*   | R_IfTru (g: ECCAenv) (e1 e2: ECCAexp) :
    ECCA_RedR g (eIf eTru e1 e2) e1
  | R_IfFls (g: ECCAenv) (e1 e2: ECCAexp) :
    ECCA_RedR g (eIf eFls e1 e2) e2
  | R_Subst (g: ECCAenv) (e e': ECCAexp) :
    ECCA_RedR g (eSubst e e e') e' *)
.
Hint Constructors ECCA_RedR.
Bind Scope ECCA_scope with ECCA_RedR.

(* Reflective Transitive Closure of step*)
Inductive ECCA_RedClosR : ECCAenv -> ECCAexp -> ECCAexp -> Prop :=
  | R_RedR (g g': ECCAenv) (e e': ECCAexp): (* maybe don't need this one? it follows from refl + trans*)
      ECCA_RedR g e e' ->
      ECCA_RedClosR g e e'
  | R_Refl (g: ECCAenv) (e: ECCAexp):
      ECCA_RedClosR g e e
  | R_Trans (g: ECCAenv) (e e' e'': ECCAexp) :
      ECCA_RedClosR g e e' ->
      ECCA_RedClosR g e' e'' ->
      ECCA_RedClosR g e e''
  | R_CongLet (g: ECCAenv) (e: ECCAexp) (e1 e2: ECCAexp) (x: atom) :
      ECCA_RedClosR (Def g x e) e1 e2 ->
      ECCA_RedClosR g (eLet x e e1) (eLet x e e2)
  | R_CongLam1 (g: ECCAenv) (A: ECCAexp) (A' e e': ECCAexp) (x: atom) :
      ECCA_RedClosR g A A' ->
      ECCA_RedClosR (Assum g x A) e e' ->
      ECCA_RedClosR g (eAbs x A e) (eAbs x A' e')
  | R_CongPi (g: ECCAenv) (A: ECCAexp) (A' B B': ECCAexp) (x: atom) :
      ECCA_RedClosR g A A' ->
      ECCA_RedClosR (Assum g x A) B B' ->
      ECCA_RedClosR g (ePi x A B) (ePi x A' B')
  | R_CongSig (g: ECCAenv) (A: ECCAexp) (A' B B': ECCAexp) (x: atom) :
      ECCA_RedClosR g A A' ->
      ECCA_RedClosR (Assum g x A) B B' ->
      ECCA_RedClosR g (eSig x A B) (eSig x A' B')
  | R_CongPair (g: ECCAenv) (e1 e1' e2 e2' A A': ECCAexp) :
      ECCA_RedClosR g e1 e1' ->
      ECCA_RedClosR g e2 e2' ->
      ECCA_RedClosR g A A'   ->
      ECCA_RedClosR g (ePair e1 e2 A) (ePair e1' e2' A')
  | R_CongApp (g: ECCAenv) (e1 e1' e2 e2': ECCAexp) :
      ECCA_RedClosR g e1 e1' ->
      ECCA_RedClosR g e2 e2' ->
      ECCA_RedClosR g (eApp e1 e2) (eApp e1' e2')
  | R_CongFst (g: ECCAenv) (V V': ECCAexp) :
      ECCA_RedClosR g V V' ->
      ECCA_RedClosR g (eFst V) (eFst V')
  | R_CongSnd (g: ECCAenv) (V V': ECCAexp) :
      ECCA_RedClosR g V V' ->
      ECCA_RedClosR g (eSnd V) (eSnd V')
(*   | R_CongIf (g: ECCAenv) (e e' e1 e1' e2 e2': ECCAexp) :
      ECCA_RedClosR g e e' ->
      ECCA_RedClosR g e1 e1' ->
      ECCA_RedClosR g e2 e2' ->
      ECCA_RedClosR g (eIf e e1 e2) (eIf e' e1' e2')
  | R_CongSubst (g: ECCAenv) (e1 e1' e2 e2' e e': ECCAexp):
      ECCA_RedClosR g e1 e1' ->
      ECCA_RedClosR g e2 e2' ->
      ECCA_RedClosR g e e' ->
      ECCA_RedClosR g (eSubst e1 e2 e) (eSubst e1' e2' e') *)
.
Notation "g '|-' e1 '=r>' e2":= (ECCA_RedClosR g e1 e2) (at level 250, e1 at level 99): ECCA_scope.
(* TODO: rewrite with notation for readability *)
Hint Constructors ECCA_RedClosR.
Bind Scope ECCA_scope with ECCA_RedClosR.
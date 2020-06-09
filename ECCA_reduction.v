Require Export ECCA_core.


(*
=====================================
=======--Reduction Relation--========
=====================================
*)

(* -Step- *)
Inductive ECCA_RedR : ECCAenv -> ECCAexp -> ECCAexp -> Prop :=
  | R_ID (g: ECCAenv) (x: atom) (e' A: ECCAexp) :
    (has g x (Def e' A)) -> ECCA_RedR g (eId x) e'
  | R_App (g: ECCAenv) (A body arg: ECCAexp) :
    ECCA_RedR g (eApp (eAbs A body) arg) (bind arg body) 
  | R_Fst (g: ECCAenv) (e1 e2 A: ECCAexp) :
    ECCA_RedR g (eFst (ePair e1 e2 A)) e1
  | R_Snd (g: ECCAenv) (e1 e2 A: ECCAexp) :
    ECCA_RedR g (eSnd (ePair e1 e2 A)) e2
  | R_Let (g: ECCAenv) (e1 e2: ECCAexp) :
    ECCA_RedR g (eLet e1 e2) (bind e1 e2)  
  | R_IfTru (g: ECCAenv) (e1 e2: ECCAexp) :
    ECCA_RedR g (eIf eTru e1 e2) e1
  | R_IfFls (g: ECCAenv) (e1 e2: ECCAexp) :
    ECCA_RedR g (eIf eFls e1 e2) e2
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
  | R_CongLet (g: ECCAenv) (e: ECCAexp) (e1 e2 A: ECCAexp) (x: name) :
(* FIXME: Why don't we reduce e? *)
      ECCA_RedClosR (g & x ~ Def e A) (open x e1) (open x e2) -> (*FIXME: where does A come from *)
      ECCA_RedClosR g (eLet e e1) (eLet e e2) 
  | R_CongLam1 (g: ECCAenv) (A: ECCAexp) (A' e e': ECCAexp) (x: name)   :
      ECCA_RedClosR g A A' ->
      ECCA_RedClosR (g & x ~ Assum A) (open x e) (open x e') ->
      ECCA_RedClosR g (eAbs A e) (eAbs A' e')
  | R_CongPi (g: ECCAenv) (A: ECCAexp) (A' B B': ECCAexp) (x: name) :
      ECCA_RedClosR g A A' ->
      ECCA_RedClosR (g & x ~ Assum A) (open x B) (open x B') ->
      ECCA_RedClosR g (ePi A B) (ePi A' B')
  | R_CongSig (g: ECCAenv) (A: ECCAexp) (A' B B': ECCAexp) (x: name) :
      ECCA_RedClosR g A A' ->
      ECCA_RedClosR (g & x ~ Assum A) (open x B) (open x B') ->
      ECCA_RedClosR g (eSig A B) (eSig A' B')
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
  | R_CongIf (g: ECCAenv) (e e' e1 e1' e2 e2': ECCAexp) :
      ECCA_RedClosR g e e' ->
      ECCA_RedClosR g e1 e1' ->
      ECCA_RedClosR g e2 e2' ->
      ECCA_RedClosR g (eIf e e1 e2) (eIf e' e1' e2')
.
Notation "g '|-' e1 '=r>' e2":= (ECCA_RedClosR g e1 e2) (at level 250, e1 at level 99): ECCA_scope.
(* TODO: rewrite with notation for readability *)
Hint Constructors ECCA_RedClosR.
Bind Scope ECCA_scope with ECCA_RedClosR.

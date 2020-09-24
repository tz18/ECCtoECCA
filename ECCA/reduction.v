Require Export core.


(*
=====================================
=======--Reduction Relation--========
=====================================
*)

(* -Step- *)
Inductive RedStep : env -> exp -> exp -> Prop :=
  | R_ID (g: env) (x: atom) (e' A: exp) :
    (has g x (Def e' A)) -> RedStep g (eId x) e'
  | R_App (g: env) (A body arg: exp) :
    RedStep g (eApp (eAbs A body) arg) (bind arg body) 
  | R_Fst (g: env) (e1 e2 A: exp) :
    RedStep g (eFst (ePair e1 e2 A)) e1
  | R_Snd (g: env) (e1 e2 A: exp) :
    RedStep g (eSnd (ePair e1 e2 A)) e2
  | R_Let (g: env) (e1 e2: exp) :
    RedStep g (eLet e1 e2) (bind e1 e2)  
  | R_IfTru (g: env) (e1 e2: exp) :
    RedStep g (eIf eTru e1 e2) e1
  | R_IfFls (g: env) (e1 e2: exp) :
    RedStep g (eIf eFls e1 e2) e2
.
Hint Constructors RedStep.
Bind Scope ECCA_scope with RedStep.



(* Reflective Transitive Closure of step*)
Inductive RedClos : env -> exp -> exp -> Prop :=
  | R_RedR (g: env) (e e': exp): (* maybe don't need this one? it follows from refl + trans*)
      RedStep g e e' ->
      RedClos g e e'
  | R_Refl (g: env) (e: exp):
      RedClos g e e
  | R_Trans (g: env) (e e' e'': exp) :
      RedClos g e e' ->
      RedClos g e' e'' ->
      RedClos g e e''
  | R_CongLet (g: env) (e e': exp) (e1 e2 A: exp) (x: name) :
      RedClos g e e' ->
      RedClos (g & x ~ Def e A) (open x e1) (open x e2) -> (*FIXME: where does A come from *)
      RedClos g (eLet e e1) (eLet e' e2) 
  | R_CongLam1 (g: env) (A: exp) (A' e e': exp) (x: name)   :
      RedClos g A A' ->
      RedClos (g & x ~ Assum A) (open x e) (open x e') ->
      RedClos g (eAbs A e) (eAbs A' e')
  | R_CongPi (g: env) (A: exp) (A' B B': exp) (x: name) :
      RedClos g A A' ->
      RedClos (g & x ~ Assum A) (open x B) (open x B') ->
      RedClos g (ePi A B) (ePi A' B')
  | R_CongSig (g: env) (A: exp) (A' B B': exp) (x: name) :
      RedClos g A A' ->
      RedClos (g & x ~ Assum A) (open x B) (open x B') ->
      RedClos g (eSig A B) (eSig A' B')
  | R_CongPair (g: env) (e1 e1' e2 e2' A A': exp) :
      RedClos g e1 e1' ->
      RedClos g e2 e2' ->
      RedClos g A A'   ->
      RedClos g (ePair e1 e2 A) (ePair e1' e2' A')
  | R_CongApp (g: env) (e1 e1' e2 e2': exp) :
      RedClos g e1 e1' ->
      RedClos g e2 e2' ->
      RedClos g (eApp e1 e2) (eApp e1' e2')
  | R_CongFst (g: env) (V V': exp) :
      RedClos g V V' ->
      RedClos g (eFst V) (eFst V')
  | R_CongSnd (g: env) (V V': exp) :
      RedClos g V V' ->
      RedClos g (eSnd V) (eSnd V')
  | R_CongIf (g: env) (e e' e1 e1' e2 e2': exp) :
      RedClos g e e' ->
      RedClos g e1 e1' ->
      RedClos g e2 e2' ->
      RedClos g (eIf e e1 e2) (eIf e' e1' e2')
.
Notation "g '|-' e1 '=r>' e2":= (RedClos g e1 e2) (at level 250, e1 at level 99): ECCA_scope.
(* TODO: rewrite with notation for readability *)
Hint Constructors RedClos.
Bind Scope ECCA_scope with RedClos.

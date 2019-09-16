(*From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Init.Datatypes.*)
Require Import Metalib.Metatheory.
Require Import Omega.


(* Module ECC. *)

(* -=ECC Definition=- *)

Inductive ECCexp: Type :=
  | eId (x: atom)
  | eUni
  | eAbs (x: atom) (A e: ECCexp)
  | eApp  (e1 e2: ECCexp)
.

Fixpoint ECCsize (e: ECCexp) : nat :=
  match e with
  | eId _ => 1
  | eUni => 1
  | eAbs _ A e => 1 + (ECCsize A) + (ECCsize e)
  | eApp e1 e2 => 1 + (ECCsize e1) + (ECCsize e2)
end.

Hint Constructors ECCexp.

Lemma ECCsize_non_zero : forall e, 0 < ECCsize e.
Proof.
  induction e; simpl; omega.
Qed.

(* -=ECC Evaluation=- *)

Definition X:= (fresh nil).
Definition Y := (fresh [ X ]).
Definition Z := (fresh (X :: Y :: nil)).

(* Substitution *)
Fixpoint FV (e: ECCexp) : atoms :=
match e with
  | eId x => singleton x
  | eUni => empty
  | eAbs x A e => FV A `union` (remove  x (FV e))
  | eApp  e1 e2 => (union (FV e1) (FV e2))
end.

Fixpoint V (e: ECCexp) : atoms :=
match e with
  | eId x => singleton x
  | eUni => empty
  | eAbs x A e => (add x (V A `union` V e))
  | eApp  e1 e2 => (union (V e1) (V e2))
end.

Compute (FV (eId X)).
Compute (FV (eApp (eId X) (eId X))).
Compute (FV (eApp (eId X) (eId Y))).
Compute (FV (eAbs X (eId Y) (eId Z))).
Example freshie := atom_fresh ((FV (eApp (eId X) (eId Y))) `union` (V (eAbs X (eId Y) (eId Z)))).
Compute freshie.
Compute (V (eAbs X (eId Y) (eId Z))).
Compute (FV (eAbs X (eId X) (eId Z))).
Compute (FV (eAbs X (eId Z) (eId X))).
Compute (FV (eAbs X (eId X) (eId X))).

(* If there are no free variables in the substitute,
   then substitution is simple.  *)

Fixpoint graft (x: atom) (arg body: ECCexp) :=
match body with
  | eId x' => if (x == x') then arg else body
  | eAbs x' A e =>
      if (x == x')
        then (eAbs x' (graft x arg A) e)
        else (eAbs x' (graft x arg A) (graft x arg e))
  | eApp e1 e2 => (eApp (graft x arg e1) (graft x arg e2))
  | eUni => body
end.

(* If there are free variables in the substitute,
   and if the term being substituted in binds one of them,
   then we need to perform an alpha conversion of the term being substituted in
   that avoids capturing any free variables in the substitute or in the body
   of the term being substituted in. *)

(* Cannot guess decreasing argument of fix :( *)

Lemma graft_id_size_preserving : forall xnew x' e, (ECCsize (graft x' (eId xnew) e)) = ECCsize e.
  intros. induction e. 
    - simpl. destruct (x' == x); auto.
    - auto.
    - simpl. destruct (x' == x).
      + cbn. rewrite -> IHe1. reflexivity.
      + cbn. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
    - cbn. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
Defined.

Definition swap_var (x:atom) (y:atom) (z:atom) :=
  if (z == x) then y else if (z == y) then x else z.

Fixpoint swap (x:atom) (y:atom) (t:ECCexp) : ECCexp :=
  match t with
  | eId z     => eId (swap_var x y z)
  | eAbs z A t1  => eAbs (swap_var x y z) (swap x y A) (swap x y t1)
  | eApp t1 t2 => eApp (swap x y t1) (swap x y t2)
  | eUni => t
  end.

Lemma swap_size_eq : forall x y t,
    ECCsize (swap x y t) = ECCsize t.
Proof.
  induction t; simpl; auto.
Qed.

Program Fixpoint trickySubst (x: atom) (arg body: ECCexp) (FVInArg: atoms) {measure (ECCsize body)}:=
match body with
  | eId x' => if (x == x') then arg else body
  | eAbs x' A e =>
      if (x == x')
        then (eAbs x' (trickySubst x arg A FVInArg) e)
        else let (xnew, _) := atom_fresh (FVInArg `union` (FV e)) in
                    (eAbs xnew (trickySubst x arg A FVInArg) (trickySubst x arg (swap x' xnew e) FVInArg))
  | eApp e1 e2 => (eApp (trickySubst x arg e1 FVInArg) (trickySubst x arg e2 FVInArg))
  | eUni => body
end.
Solve Obligations with (Tactics.program_simpl; simpl; omega).
Solve Obligations with (Tactics.program_simpl; simpl; rewrite -> swap_size_eq; omega).

Timeout 30 Compute trickySubst X (eUni) (eId X) (FV eUni). 
Compute trickySubst X (eUni) (eAbs Y (eUni) (eId X)) empty.
Compute subst x (eTru) (eAbs x (eId x) (eId x)).

(* -Step- *)
Inductive ECC_RedR : ECCenv -> ECCexp -> ECCexp -> Prop :=
  | R_ID (g: ECCenv) (x: string) (e': ECCexp) :
    ECC_LookupR g x e' -> ECC_RedR g (eId x) e'
  | R_App (g: ECCenv) (x: string) (A body arg: ECCexp) :
    ECC_RedR g (eApp (eAbs x A body) arg) (subst x arg body) (*do anything with env here?*)
  | R_Fst (g: ECCenv) (e1 e2 A: ECCexp) :
    ECC_RedR g (eFst (ePair e1 e2 A)) e1
  | R_Snd (g: ECCenv) (e1 e2 A: ECCexp) :
    ECC_RedR g (eSnd (ePair e1 e2 A)) e2
  | R_Let (g: ECCenv) (x: string) (e1 e2: ECCexp) :
    ECC_RedR g (eLet x e1 e2) (subst x e1 e2)  (*or here?*)
  | R_IfTru (g: ECCenv) (e1 e2: ECCexp) :
    ECC_RedR g (eIf eTru e1 e2) e1
  | R_IfFls (g: ECCenv) (e1 e2: ECCexp) :
    ECC_RedR g (eIf eFls e1 e2) e2
.

(* Reflective Transitive Closure of step*)
Inductive ECC_RedClosR : ECCenv -> ECCexp -> ECCexp -> Prop :=
  (*| R_RedR (g g': ECCenv) (e e': ECCexp): (* maybe don't need this one? it follows from refl + trans*)
      ECC_RedR g e g' e' ->
      ECC_RedClosR g e g' e'*)
  | R_Refl (g: ECCenv) (e: ECCexp):
      ECC_RedClosR g e e
  | R_Trans (g: ECCenv) (e e' e'': ECCexp) :
      ECC_RedR g e e' ->
      ECC_RedClosR g e' e'' ->
      ECC_RedClosR g e e''
  | R_CongLet (g: ECCenv) (e e1 e2: ECCexp) (x: string) :
      ECC_RedClosR (gAssign g x e) e1 e2 ->
      ECC_RedClosR g (eLet x e e1) (eLet x e e2)
  | R_CongLam1 (g: ECCenv) (A A' e e': ECCexp) (x: string) :
      ECC_RedClosR g A A' ->
      ECC_RedClosR (gTypeDec g x A) e e' ->
      ECC_RedClosR g (eAbs x A e) (eAbs x A' e')
  | R_CongPi (g: ECCenv) (A A' B B': ECCexp) (x: string) :
      ECC_RedClosR g A A' ->
      ECC_RedClosR (gTypeDec g x A) B B' ->
      ECC_RedClosR g (ePi x A B) (ePi x A' B')
  | R_CongSig (g: ECCenv) (A A' B B': ECCexp) (x: string) :
      ECC_RedClosR g A A' ->
      ECC_RedClosR (gTypeDec g x A) B B' ->
      ECC_RedClosR g (eSig x A B) (eSig x A' B')
  | R_CongPair (g: ECCenv) (e1 e1' e2 e2' A A': ECCexp) :
      ECC_RedClosR g e1 e1' ->
      ECC_RedClosR g e2 e2' ->
      ECC_RedClosR g A A'   ->
      ECC_RedClosR g (ePair e1 e2 A) (ePair e1' e2' A')
  | R_CongApp (g: ECCenv) (e1 e1' e2 e2': ECCexp) :
      ECC_RedClosR g e1 e1' ->
      ECC_RedClosR g e2 e2' ->
      ECC_RedClosR g (eApp e1 e2) (eApp e1' e2')
  | R_CongFst (g: ECCenv) (V V': ECCexp) :
      ECC_RedClosR g V V' ->
      ECC_RedClosR g (eFst V) (eFst V')
  | R_CongSnd (g: ECCenv) (V V': ECCexp) :
      ECC_RedClosR g V V' ->
      ECC_RedClosR g (eSnd V) (eSnd V')
  | R_CongIf (g: ECCenv) (e e' e1 e1' e2 e2': ECCexp) :
      ECC_RedClosR g e e' ->
      ECC_RedClosR g e1 e1' ->
      ECC_RedClosR g e2 e2' ->
      ECC_RedClosR g (eIf e e1 e2) (eIf e' e1' e2')
.

(* Congruence conversion?*)

Inductive ECC_CongConv: ECCenv -> ECCexp -> ECCexp -> Prop :=
  | C_Cong (g: ECCenv) (e e1 e2: ECCexp) :
      ECC_RedClosR g e1 e ->
      ECC_RedClosR g e2 e ->
      ECC_CongConv g e1 e2
  | C_CongIta1 (g: ECCenv) (e1 A e e2 e2': ECCexp) (x: string) :
      ECC_RedClosR g e1 (eAbs x A e) ->
      ECC_RedClosR g e2 e2' ->
      ECC_CongConv (gTypeDec g x A) e (eApp e2' (eId x)) ->
      ECC_CongConv g e1 e2
  | C_CongIta2 (g: ECCenv) (e e1 e1' e2 A : ECCexp) (x: string) :
      ECC_RedClosR g e1 e1' ->
      ECC_RedClosR g e2 (eAbs x A e) ->
      ECC_CongConv (gTypeDec g x A) (eApp e1' (eId x)) e ->
      ECC_CongConv g e1 e2
.

(* Typing *)

Inductive ECC_sub_type: ECCenv -> ECCexp -> ECCexp -> Prop :=
| ST_Cong (g: ECCenv) (A B: ECCexp) :
  ECC_CongConv g A B ->
  ECC_sub_type g A B
| ST_Cum (g: ECCenv) (i: nat) :
  ECC_sub_type g (eUni (uType i)) (eUni (uType (S i)))
| ST_Pi (g: ECCenv) (A1 A2 B1 B2: ECCexp) (x1 x2: string) :
  (ECC_CongConv g A1 A2) ->
  (ECC_sub_type (gTypeDec g x1 A2) B1 (subst x2 (eId x1) B2)) -> (* eId x1 ?*)
  (ECC_sub_type g (ePi x1 A1 B1) (ePi x2 A2 B2))
.

Inductive ECC_has_type: ECCenv -> ECCexp -> ECCexp -> Prop :=
| T_Ax_Prop (g: ECCenv) :
  (ECC_has_type g (eUni uProp) (eUni (uType 0)))
| T_Ax_Type (g: ECCenv) (i: nat) :
  (ECC_has_type g (eUni (uType i)) (eUni (uType (S i))))
| T_Var (g: ECCenv) (x: string) (A: ECCexp) :
  (ECC_LookupR g x A) -> (* this needs adjustment *)
  (ECC_has_type g (eId x) A)
| T_Let (g: ECCenv) (e e' A B: ECCexp) (x: string):
  (ECC_has_type g e A) ->
  (ECC_has_type (gAssign (gTypeDec g x A) x e) e' B) ->
  (ECC_has_type g (eLet x e e') (subst x e B))
| T_Prod_Prop (g: ECCenv) (x: string) (A B: ECCexp) (i: nat):
  (ECC_has_type g A (eUni (uType i))) ->
  (ECC_has_type (gTypeDec g x A) B (eUni (uProp))) ->
  (ECC_has_type g (ePi x A B) (eUni (uProp)))
| T_Prod_Type (g: ECCenv) (x: string) (A B: ECCexp) (i: nat):
  (ECC_has_type g A (eUni (uType i))) ->
  (ECC_has_type (gTypeDec g x A) B (eUni (uType i))) ->
  (ECC_has_type g (ePi x A B) (eUni (uType i)))
| T_Lam (g: ECCenv) (x: string) (A e B: ECCexp) :
  (ECC_has_type (gAssign g x A) e B) ->
  (ECC_has_type g (eAbs x A e) (ePi x A B))
| T_App (g: ECCenv) (x: string) (e e' A' B: ECCexp) :
  (ECC_has_type g e (ePi x A' B)) ->
  (ECC_has_type g e' A') ->
  (ECC_has_type g (eApp e e') (subst x e B))
| T_Sig (g: ECCenv) (x: string) (A B: ECCexp) (i: nat) :
  (ECC_has_type g A (eUni (uType i))) ->
  (ECC_has_type (gTypeDec g x A) B (eUni (uType i))) -> (* should these be the same i*)
  (ECC_has_type g (eSig x A B) (eUni (uType i)))
| T_Pair (g: ECCenv) (e1 e2 A B: ECCexp) (x: string) :
  (ECC_has_type g e1 A) ->
  (ECC_has_type g e2 (subst x e1 B)) ->
  (ECC_has_type g (ePair e1 e2 (eSig x A B)) (eSig x A B))
| T_Fst (g: ECCenv) (e A B: ECCexp) (x: string) :
  (ECC_has_type g e (eSig x A B)) ->
  (ECC_has_type g (eFst e) A)
| T_Snd (g: ECCenv) (e A B: ECCexp) (x: string) :
  (ECC_has_type g e (eSig x A B)) ->
  (ECC_has_type g (eSnd e) (subst x (eFst e) B))
| T_Bool (g: ECCenv):
  (ECC_has_type g (eBool) (eUni (uType 0)))
| T_True (g: ECCenv):
  (ECC_has_type g (eTru) (eBool))
| T_False (g: ECCenv):
  (ECC_has_type g (eFls) (eBool))
| T_If (g: ECCenv) (B U e e1 e2: ECCexp) (x: string):
  (ECC_has_type (gTypeDec g x (eBool)) B U) ->
  (ECC_has_type g e (eBool)) ->
  (ECC_has_type g e1 (subst x (eTru) B)) ->
  (ECC_has_type g e2 (subst x (eFls) B)) ->
  (ECC_has_type g (eIf e e1 e2) (subst x e B))
| T_Conv (g: ECCenv) (e A B U: ECCexp) :
  (ECC_has_type g e A) ->
  (ECC_has_type g B U) ->
  (ECC_sub_type g A B) ->
  (ECC_has_type g e B)
.

Hint Constructors ECC_has_type.

Goal ECC_has_type gEmpty (eUni uProp) (eUni (uType 0)).
Proof.
intuition.
Qed.

(* ECC Notation *)

Bind Scope ECC_scope with ECCexp.
Bind Scope ECC_scope with ECCuni.
Bind Scope ECC_scope with ECCenv.
Delimit Scope ECC_scope with ECC.
Coercion eId: string >-> ECCexp.

Definition X := "x".
Definition F := "f".

Notation "'type' x" := (eUni (uType x)) (at level 50):  ECC_scope.
Notation "'prop'" := (eUni uProp) (at level 50):  ECC_scope.
Definition example_Type := (type 3)%ECC: ECCexp.
Definition example_Prop := (prop)%ECC: ECCexp.

Notation "{ e1 e2 }" := (eApp e1 e2) (at level 50,e1 at level 9):  ECC_scope.
Definition example_App := { "x" "y" }%ECC: ECCexp.

Notation "'LET' x ':=' A 'in' B" := (eLet x A B) (at level 50, format "'[v' 'LET'  x  ':='  A '/' 'in' '['  B ']' ']'") : ECC_scope.
Definition example_Let := (LET "x" := "c" in "d")%ECC : ECCexp.
Print example_Let.
Definition example_Let2 := (LET X := (type 3) in LET F := (LET X := (type 2) in X) in ({X F}))%ECC.
Print example_Let2.

Notation "'P' x : A '->' B" := (ePi x A B) (at level 50, x at level 9, A at level 9) : ECC_scope.
Definition example_Pi := (P "x" : "f" -> "b")%ECC : ECCexp.
Notation "'\'  x : A  '->'  B" := (eAbs x A B) (at level 50, x at level 9, A at level 9) : ECC_scope.
Definition example_Abs := (\ "x" : "a" -> "b")%ECC : ECCexp.
Notation "'M' x : A '..' B" := (eSig x A B) (at level 50, x at level 1, A at level 1): ECC_scope.
Definition example_Sig := (M "x" : "A" .. "B")%ECC : ECCexp.
Notation "< e1 , e2 > 'as' A" := (ePair e1 e2 A) (at level 50, e1 at level 5, e2 at level 5, A at level 5): ECC_scope.
Definition example_Pair := (< "x", "y" > as (M "x" : "A" .. "B"))%ECC : ECCexp.
Notation "'fst' e" := (eFst e) (at level 50, e at level 5): ECC_scope.
Notation "'snd' e" := (eSnd e) (at level 50, e at level 5): ECC_scope.

Definition example_ycombinator := (\F:(type 3) -> ({(\X:(type 2) -> ({F {X X}})) (\X:(type 2) -> ({F {X X}}))}))%ECC.
Print example_ycombinator.

Print (size example_ycombinator).


(* End ECC.*)


(* Module ECCA. *)

(* -=ECCA Definition=- *)

Inductive ECCAsym: Type:=
  | asymStr (x: string)
  | asymNum (x: nat)
.

Inductive ECCAval: Type :=
  | avId (x: ECCAsym)
  | avUni (U: ECCuni)
  | avPi (x: ECCAsym) (A B: ECCAconf)
  | avAbs (x: ECCAsym) (A B: ECCAconf)
  | avSig (x: ECCAsym) (A B: ECCAconf)
  | avPair (v1 v2: ECCAval) (A: ECCAconf)
  | avTru
  | avFls
  | avBool
  | avUndef
with
ECCAconf: Type :=
  | acfComp (e: ECCAcomp)
  | acfLet (x: ECCAsym) (A: ECCAcomp) (B: ECCAconf)
with
ECCAcomp: Type :=
  | acpApp (v1 v2: ECCAval)
  | acpVal (v: ECCAval)
  | acpFst (v: ECCAval)
  | acpSnd (v: ECCAval)
.

Inductive ECCAcont: Type :=
  | actHole
  | actLetHole (x: ECCAsym) (B: ECCAconf)
.

(* -=ECCA Notation=- *)

Bind Scope ECCA_scope with ECCAsym.
Bind Scope ECCA_scope with ECCAval.
Bind Scope ECCA_scope with ECCAconf.
Bind Scope ECCA_scope with ECCAcomp.
Bind Scope ECCA_scope with ECCAcont.
Delimit Scope ECCA_scope with ECCA.
Coercion asymStr: string >-> ECCAsym.
Coercion asymNum: nat >-> ECCAsym.
Coercion avId: ECCAsym >-> ECCAval.
Coercion acpVal: ECCAval >-> ECCAcomp.
Coercion acfComp: ECCAcomp >-> ECCAconf.
Notation "'type' x" := (avUni (uType x)) (at level 50):  ECCA_scope.
Notation "'prop'" := (avUni uProp) (at level 50):  ECCA_scope.
Definition example_aType := (type 3)%ECCA: ECCAval.
Definition example_aProp := (prop)%ECCA: ECCAval.

Notation "{ e1 e2 }" := (acpApp e1 e2) (at level 50,e1 at level 9):  ECCA_scope.
Definition example_aApp := { "x" "y" }%ECCA: ECCAcomp.

Notation "'LET' x ':=' A 'in' B" := (acfLet x A B) (at level 50, format "'[v' 'LET'  x  ':='  A '/' 'in' '['  B ']' ']'") : ECCA_scope.
Definition example_aLet := (LET "x" := "c" in "d")%ECCA : ECCAconf.
Print example_aLet.
Definition example_aLet2 := (LET X := (type 3) in LET F := (LET X := (type 2) in X) in ({X F}))%ECC.
Print example_aLet2.

Notation "'P' x : A '->' B" := (avPi x A B) (at level 50, x at level 9, A at level 9) : ECCA_scope.
Definition example_aPi := (P "x" : "f" -> "b")%ECCA : ECCAval.
Notation "'\' x : A '->' B" := (avAbs x A B) (at level 50, x at level 9, A at level 9) : ECCA_scope.
Definition example_aAbs := (\ "x" : "a" -> "b")%ECCA : ECCAval.

Notation "'[]'" := (actHole) (at level 50) : ECCA_scope.
Definition aHole := []%ECCA.
Notation "'LET' x ':=' '[]' 'in' B" := (actLetHole x B) (at level 50) : ECCA_scope.
Definition example_aLetHole := (LET "x" := [] in "x")%ECCA.
Print example_aLetHole.
(* End ECCA. *)


(* ===ECC to ECCA translation== *)


Fixpoint fill_hole (e: ECCAcomp) (K: ECCAcont): ECCAconf :=
  match K with
    | actHole => acfComp e
    | actLetHole x B => acfLet x e B
end.

(* {ns : NameState} *)
Fixpoint trans  (ns: nat) (e: ECCexp) (K: ECCAcont) : ECCAconf :=
  match e with
    | eId x => (fill_hole (acpVal (avId (asymStr x))) K)
    | ePi x A B => (fill_hole (acpVal (avPi (asymStr x) (trans ns A actHole) (trans ns B actHole))) K)
    | eAbs x A e => (fill_hole (acpVal (avAbs (asymStr x) (trans ns A actHole) (trans ns e actHole))) K)
    | eApp e1 e2 =>
        (trans (S ns) e1 (actLetHole (asymNum (S ns))
            (trans (S (S ns)) e2 (actLetHole (asymNum (S (S ns)))
                (fill_hole (acpApp (avId (asymNum (S ns))) (avId (asymNum (S (S ns))))) K)))))
    | eLet x e1 e2 => (trans ns e1 (actLetHole (asymStr x)
                          (trans (ns) e2 K)))
    | eSig x A B => (fill_hole (acpVal (avSig (asymStr x) (trans ns A actHole) (trans ns B actHole))) K)
    | ePair e1 e2 A => (trans (S ns) e1 (actLetHole (asymNum (S ns))
            (trans (S (S ns)) e2 (actLetHole (asymNum (S (S ns)))
               (trans (S (S (S ns))) A (actLetHole (asymNum (S (S (S ns))))
                (fill_hole (avPair (avId (asymNum (S ns))) (avId (asymNum (S (S ns)))) (avId (asymNum (S (S (S ns)))))) K)))))))
    | eFst e => (trans (S ns) e (actLetHole (asymNum (S ns))
                   (fill_hole (acpFst (asymNum (S ns))) K)))
    | eSnd e => (trans (S ns) e (actLetHole (asymNum (S ns))
                   (fill_hole (acpSnd (asymNum (S ns))) K)))
    | eTru => (fill_hole (acpVal avTru) K)
    | eFls => (fill_hole (acpVal avFls) K)
    | eBool=> (fill_hole (acpVal avBool) K)
    | eUni u => (fill_hole (acpVal (avUni u)) K)
end.

Check eAbs "f" (eUni (uType 1)) (eApp (eAbs "x" (eUni (uType 1)) (eApp (eId "f") (eApp (eId "x") (eId "x")))) (eAbs "x" (eUni (uType 1)) (eApp (eId "f") (eApp (eId "x") (eId "x"))))).

Compute trans 0 (eAbs "f" (eUni (uType 1)) (eApp (eAbs "x" (eUni (uType 1)) (eApp (eId "f") (eApp (eId "x") (eId "x")))) (eAbs "x" (eUni (uType 1)) (eApp (eId "f") (eApp (eId "x") (eId "x")))))) actHole.

Check (eAbs "f" (eUni (uType 1)) (eApp (eLet "lx" (eApp (eId "f") (eId "ix")) (eApp (eId "f") (eId "lx"))) (eId "f"))).
Compute trans 0 (eAbs "f" (eUni (uType 1)) (eApp (eLet "lx" (eApp (eId "f") (eId "ix")) (eApp (eId "f") (eId "lx"))) (eId "f"))) actHole.

Check {({({({"a" "b"}) "c"}) "d"}) ({({({"a" "b"}) "c"}) "d"})}%ECC.
Compute trans 0 ({({({({"a" "b"}) {"e" "c"}}) "d"}) ({({({"d" "c"}) "b"}) "a"})})%ECC actHole.

Check eSig "s" (eUni (uType 1)) (eUni (uType 2)).
Compute trans 0 (eFst (ePair "e1" "e2" (eSig "s" (eUni (uType 1)) ("s"))))%ECC actHole.

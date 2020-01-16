(*From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Init.Datatypes.*)
Require Import Atom.
(* -=ECCA Definition=- *)

(* Restricted ECCA, used in computing *)

Inductive ECCAval: Type :=
  | Id (x: atom)
  | Uni (U: ECCuni)
  | Pi (x: atom) (A B: ECCAconf)
  | Abs (x: atom) (A B: ECCAconf)
  | Sig (x: atom) (A B: ECCAconf)
  | Pair (v1 v2: ECCAval) (A: ECCAconf)
  | Tru
  | Fls
  | Bool
with
ECCAconf: Type :=
  | Comp (e: ECCAcomp)
  | Let (x: atom) (A: ECCAcomp) (B: ECCAconf)
  | If (v: ECCAval) (m1 m2: ECCAconf)
with
ECCAcomp: Type :=
  | App (v1 v2: ECCAval)
  | Val (v: ECCAval)
  | Fst (v: ECCAval)
  | Snd (v: ECCAval)
  | Subst (x arg body: ECCAval)
.

Inductive ECCAcont: Type :=
  | Hole
  | LetHole (x: atom) (B: ECCAconf)
.

Inductive ECCAexp: Type :=
  | eId (x: atom)
  | eUni (U: ECCuni)
  | ePi (x: atom) (A B: ECCAexp)
  | eAbs (x: atom) (A B: ECCAexp)
  | eSig (x: atom) (A B: ECCAexp)
  | ePair (v1 v2: ECCAexp) (A: ECCAexp)
  | eTru
  | eFls
  | eBool
  | eLet (x: atom) (A: ECCAexp) (B: ECCAexp)
  | eIf (v: ECCAexp) (m1 m2: ECCAexp)
  | eApp (v1 v2: ECCAexp)
  | eFst (v: ECCAexp)
  | eSnd (v: ECCAexp)
  | eSubst (x arg body: ECCAexp)
.

Inductive ECCAenv: Type :=
  | Empty
  | Assum (g: ECCAenv) (x: atom) (A: ECCAexp)
  | Def (g: ECCAenv) (x: atom) (v: ECCAexp)
  | Eq (g: ECCAenv) (v1 v2: ECCAexp)
.

Fixpoint flattenECCAval (e: ECCAval): ECCAexp :=
match e with
  | Id x => eId x
  | Uni U => eUni U
  | Pi x A B => ePi x (flattenECCAconf A) (flattenECCAconf B) 
  | Abs x A B => eAbs x (flattenECCAconf A) (flattenECCAconf B)
  | Sig x A B => eSig x (flattenECCAconf A) (flattenECCAconf B)
  | Pair v1 v2 A => ePair (flattenECCAval v1) (flattenECCAval v2) (flattenECCAconf A)
  | Tru => eTru
  | Fls => eFls
  | Bool => eBool
end
with flattenECCAcomp (e: ECCAcomp): ECCAexp :=
match e with
  | App v1 v2 => eApp (flattenECCAval v1) (flattenECCAval v2)
  | Val v => flattenECCAval v
  | Fst v => eFst (flattenECCAval v)
  | Snd v => eSnd (flattenECCAval v)
  | Subst x arg body => eSubst (flattenECCAval x) (flattenECCAval arg) (flattenECCAval body)
end
with flattenECCAconf (e: ECCAconf): ECCAexp :=
match e with
  | Comp e => flattenECCAcomp e
  | Let x A B => eLet x (flattenECCAcomp A) (flattenECCAconf B)
  | If v m1 m2 => eIf (flattenECCAval v) (flattenECCAconf m1) (flattenECCAconf m2)
end.


Coercion Val: ECCAval >-> ECCAcomp. 
Coercion Comp: ECCAcomp >-> ECCAconf. 
Coercion flattenECCAval: ECCAval >-> ECCAexp.
Coercion flattenECCAcomp: ECCAcomp >-> ECCAexp.
Coercion flattenECCAconf: ECCAconf >-> ECCAexp.

Inductive ECCA_LookupTypeR : ECCAenv -> atom -> ECCAexp -> Prop:=
  | aLT_gFirst (g': ECCAenv) (x: atom) (A: ECCAval):
      ECCA_LookupTypeR (Assum g' x A) x A
  | aLT_AssumRest (g: ECCAenv) (x x': atom) (A a': ECCAval):
      ECCA_LookupTypeR g x A ->
      (x <> x') ->
      (ECCA_LookupTypeR (Assum g x' a') x A)
  | aLT_DefRest (g: ECCAenv) (x x': atom) (A a': ECCAval):
      ECCA_LookupTypeR g x A ->
  (*     (x <> x') -> *)
      (ECCA_LookupTypeR (Def g x' a') x A)
  | aLT_EqRest (g: ECCAenv) (x: atom) (v A v': ECCAval):
      ECCA_LookupTypeR g x A ->
      ECCA_LookupTypeR (Eq g v v') x A 
.

Inductive ECCA_LookupDefR : ECCAenv -> atom -> ECCAexp -> Prop:=
  | aLD_gFirst (g': ECCAenv) (x: atom) (e: ECCAcomp) (A: ECCAconf):
      ECCA_LookupDefR (Assum (Def g' x e) x A) x e
  | aLD_AssumRest (g: ECCAenv) (x x': atom) (e: ECCAcomp) (a': ECCAconf):
      ECCA_LookupDefR g x e ->
      (x <> x') ->
      (ECCA_LookupDefR (Assum g x' a') x e)
  | aLD_DefRest (g: ECCAenv) (x x': atom) (e e': ECCAcomp):
      ECCA_LookupDefR g x e ->
      (x <> x') ->
      (ECCA_LookupDefR (Def g x' e') x e)
  | aLD_EqRest (g: ECCAenv) (x: atom) (v v': ECCAval) (e: ECCAcomp):
      ECCA_LookupDefR g x e ->
      ECCA_LookupDefR (Eq g v v') x e 
.

(*should change val to conf *)
Inductive ECCA_LookupEqR : ECCAenv -> ECCAexp -> ECCAexp -> Prop:=
  | aLE_gFirst (g': ECCAenv) (v v': ECCAval):
    ECCA_LookupEqR (Eq g' v v') v v'
  | aLE_AssumRest (g: ECCAenv) (x : atom) (v v' a: ECCAval):
      ECCA_LookupEqR g v v' ->
      (ECCA_LookupEqR (Assum g x a) v v')
  | aLE_DefRest (g: ECCAenv) (x: atom) (v v' e: ECCAval):
      ECCA_LookupEqR g v v' ->
      (ECCA_LookupEqR (Def g x e) v v')
  | aLE_EqRest (g: ECCAenv) (x: atom) (v1 v2 v1' v2': ECCAval):
      ECCA_LookupEqR g v1 v2 ->
      (v1 <> v1') ->
      ECCA_LookupEqR (Eq g v1' v2') v1 v2 
.

Fixpoint FV (e: ECCAexp) : atoms :=
match e with
  | eId x => singleton x
  | eUni U => empty
  | ePi x A B =>  union (FV A) (remove x (FV B))
  | eAbs x A e => union (FV A) (remove  x (FV e))
  | eApp  e1 e2 => (union (FV e1) (FV e2))
  | eLet x e1 e2 => (union (FV e1) (FV e2))
  | eSig x A B => (union (FV A) (remove  x (FV B)))
  | ePair e1 e2 A => (union (union  (FV e1) (FV e2)) (FV A))
  | eFst e => (FV e)
  | eSnd e => (FV e)
  | eIf e e1 e2 => (union (union  (FV e) (FV e1)) (FV e2))
  | _ => empty
end.

(*Let's get nominal!*)

Fixpoint swap (x:atom) (y:atom) (t:ECCAexp) : ECCAexp :=
  match t with
  | eId z     => eId (swap_var x y z)
  | eAbs z A t1  => eAbs (swap_var x y z) (swap x y A) (swap x y t1)
  | eApp t1 t2 => eApp (swap x y t1) (swap x y t2)
  | ePi x' A B => ePi (swap_var x y x') (swap x y A) (swap x y B)
  | eLet x' e1 e2 => eLet (swap_var x y x') (swap x y e1) (swap x y e2)
  | eSig x' A B => eSig (swap_var x y x') (swap x y A) (swap x y B)
  | ePair e1 e2 A => ePair (swap x y e1) (swap x y e2) (swap x y A)
  | eFst e => (eFst (swap x y e))
  | eSnd e => (eSnd (swap x y e))
  | eIf e e1 e2 => (eIf (swap x y e) (swap x y e1) (swap x y e2))
  | _ => t
  end.

Fixpoint ECCAsize (e: ECCAexp) : nat :=
  match e with
  | eId _ => 1
  | eUni _ => 1
  | ePi _ A B => 1 + (ECCAsize A) + (ECCAsize B)
  | eAbs _ A e => 1 + (ECCAsize A) + (ECCAsize e)
  | eApp e1 e2 => 1 + (ECCAsize e1) + (ECCAsize e2)
  | eLet _ e1 e2 => 1 + (ECCAsize e1) + (ECCAsize e2)
  | eSig _ A B => 1 + (ECCAsize A) + (ECCAsize B)
  | ePair e1 e2 A => 1 + (ECCAsize e1) + (ECCAsize e2) + (ECCAsize A)
  | eFst e => 1 + (ECCAsize e)
  | eSnd e => 1 + (ECCAsize e)
  | eIf e e1 e2 => 1 + (ECCAsize e) + (ECCAsize e1) + (ECCAsize e2)
  | eSubst a b c => 1 + (ECCAsize a) + (ECCAsize b) + (ECCAsize c)
  | _ => 1
end.

Lemma ECCAsize_non_zero : forall e, 0 < ECCAsize e.
Proof.
  induction e; simpl; omega.
Qed.

Lemma swap_size_eq : forall x y t,
    ECCAsize (swap x y t) = ECCAsize t.
Proof.
  induction t; simpl; auto.
Qed.


(* If there are free variables in the substitute,
   and if the term being substituted in binds one of them,
   then we need to perform an alpha conversion of the term being substituted in
   that avoids capturing any free variables in the substitute or in the body
   of the term being substituted in. *)

Program Fixpoint substWork (x: atom) (arg body: ECCAexp) (FVInArg: atoms) {measure (ECCAsize body)}:=
match body with
  | eId x' => if (x =? x') then arg else body
  | eAbs x' A e =>
      if (x =? x')
        then (eAbs x' (substWork x arg A FVInArg) e)
        else let xnew := fresh (union FVInArg (FV e)) in
                    (eAbs xnew (substWork x arg A FVInArg) (substWork x arg (swap x' xnew e) FVInArg))
  | ePi x' A B =>
      if (x =? x')
        then (ePi x' (substWork x arg A FVInArg) B)
        else let xnew := fresh (union FVInArg (FV B)) in
                (ePi xnew (substWork x arg A FVInArg) (substWork x arg (swap x' xnew B) FVInArg))
  | eLet x' A B =>
      if (x =? x')
        then (eLet x' (substWork x arg A FVInArg) B)
        else let xnew := fresh (union FVInArg (FV B)) in
                (eLet xnew (substWork x arg A FVInArg) (substWork x arg (swap x' xnew B) FVInArg))
  | eSig x' A B =>
      if (x =? x')
        then (eSig x' (substWork x arg A FVInArg) B)
        else let xnew := fresh (union FVInArg (FV B)) in
                (eSig xnew (substWork x arg A FVInArg) (substWork x arg (swap x' xnew B) FVInArg))
  | eApp e1 e2 => (eApp (substWork x arg e1 FVInArg) (substWork x arg e2 FVInArg))
  | eUni U => body
  | ePair e1 e2 A => (ePair (substWork x arg e1 FVInArg) (substWork x arg e2 FVInArg) (substWork x arg A FVInArg))
  | eFst e => (eFst (substWork x arg e FVInArg))
  | eSnd e => (eSnd (substWork x arg e FVInArg))
  | eIf e e1 e2 => (eIf (substWork x arg e FVInArg) (substWork x arg e1 FVInArg) (substWork x arg e2 FVInArg))
  | eTru => eTru
  | eFls => eFls
  | eBool => eBool
  | eSubst a b c => eSubst (substWork x arg a FVInArg) (substWork x arg b FVInArg) (substWork x arg c FVInArg) (**)
end.
Obligations.
Solve Obligations with (Tactics.program_simpl; cbn; omega).
Solve Obligations with (Tactics.program_simpl; cbn; rewrite -> swap_size_eq; omega).

Definition subst (x: atom) (arg body: ECCAexp):= substWork x arg body (FV arg).

Inductive ECCA_Aeq : ECCAexp -> ECCAexp -> Prop :=
  | aeq_id (e: ECCAexp):
    ECCA_Aeq e e
  | aeq_var (x: atom):
     ECCA_Aeq (eId x) (eId x)
  | aeq_abs_same (x: atom) (t1 t2 b1 b2: ECCAexp):
     ECCA_Aeq t1 t2 -> 
     ECCA_Aeq b1 b2 ->
     ECCA_Aeq (eAbs x t1 b1) (eAbs x t2 b2)
  | aeq_abs_diff (x y: atom) (t1 t2 b1 b2: ECCAexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECCA_Aeq b1 (swap y x b2) ->
     ECCA_Aeq t1 t2 ->
     ECCA_Aeq (eAbs x t1 b1) (eAbs y t2 b2)
  | aeq_pi_same (x: atom) (t1 t2 b1 b2: ECCAexp):
     ECCA_Aeq t1 t2 -> 
     ECCA_Aeq b1 b2 ->
     ECCA_Aeq (ePi x t1 b1) (ePi x t2 b2)
  | aeq_pi_diff (x y: atom) (t1 t2 b1 b2: ECCAexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECCA_Aeq b1 (swap y x b2) ->
     ECCA_Aeq t1 t2 ->
     ECCA_Aeq (ePi x t1 b1) (ePi y t2 b2)
  | aeq_let_same (x: atom) (t1 t2 b1 b2: ECCAexp):
     ECCA_Aeq t1 t2 -> 
     ECCA_Aeq b1 b2 ->
     ECCA_Aeq (eLet x t1 b1) (eLet x t2 b2)
  | aeq_let_diff (x y: atom) (t1 t2 b1 b2: ECCAexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECCA_Aeq b1 (swap y x b2) ->
     ECCA_Aeq t1 t2 ->
     ECCA_Aeq (eLet x t1 b1) (eLet y t2 b2)
  | aeq_sig_same (x: atom) (t1 t2 b1 b2: ECCAexp):
     ECCA_Aeq t1 t2 -> 
     ECCA_Aeq b1 b2 ->
     ECCA_Aeq (eSig x t1 b1) (eSig x t2 b2)
  | aeq_sig_diff (x y: atom) (t1 t2 b1 b2: ECCAexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECCA_Aeq b1 (swap y x b2) ->
     ECCA_Aeq t1 t2 ->
     ECCA_Aeq (eSig x t1 b1) (eSig y t2 b2)
  | aeq_app (t1 t2 t1' t2': ECCAexp):
     ECCA_Aeq t1 t1' -> ECCA_Aeq t2 t2' ->
     ECCA_Aeq (eApp t1 t2) (eApp t1' t2')
  | aeq_pair (t1 t2 t1' t2' A A': ECCAexp):
     ECCA_Aeq t1 t1' -> ECCA_Aeq t2 t2' ->
     ECCA_Aeq A A' ->
     ECCA_Aeq (ePair t1 t2 A) (ePair t1' t2' A')
  | aeq_Fst (e e': ECCAexp):
     ECCA_Aeq e e' ->
     ECCA_Aeq (eFst e) (eFst e')
  | aeq_Snd (e e': ECCAexp):
     ECCA_Aeq e e' ->
     ECCA_Aeq (eSnd e) (eSnd e')
  | aeq_if (e1 e2 e3 e1' e2' e3': ECCAexp):
     ECCA_Aeq e1 e1' ->
     ECCA_Aeq e2 e2' ->
     ECCA_Aeq e3 e3' ->
     ECCA_Aeq (eIf e1 e2 e3) (eIf e1' e2' e3').

Hint Constructors ECCA_Aeq.

(* -Step- *)
Inductive ECCA_RedR : ECCAenv -> ECCAexp -> ECCAexp -> Prop :=
  | R_ID (g: ECCAenv) (x: atom) (e': ECCAexp) :
    ECCA_LookupDefR g x e' -> ECCA_RedR g (Id x) e'
  | R_App (g: ECCAenv) (x: atom) (A body arg: ECCAexp) :
    ECCA_RedR g (eApp (eAbs x A body) arg) (subst x arg body) (*do anything with env here?*)
  | R_Fst (g: ECCAenv) (e1 e2 A: ECCAexp) :
    ECCA_RedR g (eFst (ePair e1 e2 A)) e1
  | R_Snd (g: ECCAenv) (e1 e2 A: ECCAexp) :
    ECCA_RedR g (eSnd (ePair e1 e2 A)) e2
  | R_Let (g: ECCAenv) (x: atom) (e1 e2: ECCAexp) :
    ECCA_RedR g (eLet x e1 e2) (subst x e1 e2)  (*or here?*)
  | R_IfTru (g: ECCAenv) (e1 e2: ECCAexp) :
    ECCA_RedR g (eIf Tru e1 e2) e1
  | R_IfFls (g: ECCAenv) (e1 e2: ECCAexp) :
    ECCA_RedR g (eIf Fls e1 e2) e2
.

Hint Constructors ECCA_RedR.

(* Reflective Transitive Closure of step*)
Inductive ECCA_RedClosR : ECCAenv -> ECCAexp -> ECCAexp -> Prop :=
  (*| R_RedR (g g': ECCAenv) (e e': ECCAexp): (* maybe don't need this one? it follows from refl + trans*)
      ECCA_RedR g e e' ->
      ECCA_RedClosR g e e'*)
  | R_Refl (g: ECCAenv) (e: ECCAexp):
      ECCA_RedClosR g e e
  | R_Trans (g: ECCAenv) (e e' e'': ECCAexp) :
      ECCA_RedR g e e' ->
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
  | R_CongIf (g: ECCAenv) (e e' e1 e1' e2 e2': ECCAexp) :
      ECCA_RedClosR g e e' ->
      ECCA_RedClosR g e1 e1' ->
      ECCA_RedClosR g e2 e2' ->
      ECCA_RedClosR g (eIf e e1 e2) (eIf e' e1' e2')
.

Hint Constructors ECCA_RedClosR.


Definition conf_to_val (e: ECCAconf): option ECCAval :=
match e with
  | Comp c => match c with 
      | Val v => Some v
      | _ => None
      end
  | _ => None
  end.

Compute (conf_to_val Tru).
Compute (conf_to_val (Let X Tru Tru)).
Compute (conf_to_val (Val Tru)).
Compute (conf_to_val (Comp Tru)).

(* Lemma conf_is_val_dec: forall e: ECCAconf, 
(exists v, (conf_to_val e) = Some v) + (conf_to_val e = None). Proof.
intros. destruct e; auto.
  - destruct e; auto.
    +  *)

Inductive ECCA_Equiv: ECCAenv -> ECCAexp -> ECCAexp -> Prop :=
  | aE_Equiv (g: ECCAenv) (e e1 e2: ECCAexp) :
      ECCA_RedClosR g e1 e ->
      ECCA_RedClosR g e2 e ->
      ECCA_Equiv g e1 e2
   | aE_EquivIta1 (g: ECCAenv) (e1 A e e2 e2': ECCAexp) (e2' v2': ECCAexp) (x: atom) :
      ECCA_RedClosR g e1 (eAbs x A e) ->
      ECCA_RedClosR g e2 e2' ->
(*       conf_to_val e2' = Some v2' -> *)
      ECCA_Equiv (Assum g x A) e (eApp v2' (Id x)) ->
      ECCA_Equiv g e1 e2 
   | aE_EquivIta2 (g: ECCAenv) (e e1 e1' e2 A : ECCAexp) (e1' v1': ECCAexp) (x: atom) :
      ECCA_RedClosR g e1 e1' ->
      ECCA_RedClosR g e2 (eAbs x A e) ->
(*       conf_to_val e1' = Some v1' -> *)
      ECCA_Equiv (Assum g x A) (eApp v1' (Id x)) e ->
      ECCA_Equiv g e1 e2 
  | aE_EquivAlpha (g: ECCAenv) (e1 e2: ECCAexp):
      ECCA_Aeq e1 e2 ->
      ECCA_Equiv g e1 e2
  | aE_Subst1 (g: ECCAenv) (e e1 e2 v: ECCAexp) (e': ECCAexp):
(*       conf_to_val e = Some v -> *)
      ECCA_Equiv g e e' ->
      ECCA_Equiv g (eSubst e1 e2 v) e'
  | aE_Subst2 (g: ECCAenv) (e1 e2 v: ECCAexp) (e e': ECCAexp):
(*       conf_to_val e = Some v -> *)
      ECCA_Equiv g e e' ->
      ECCA_Equiv g e' (eSubst e1 e2 v)
.

Hint Constructors ECCA_Equiv.

Inductive ECCA_sub_type: ECCAenv -> ECCAexp -> ECCAexp -> Prop :=
| aST_Cong (g: ECCAenv) (A B: ECCAexp) :
  ECCA_Equiv g A B ->
  ECCA_sub_type g A B
| aST_Cum (g: ECCAenv) (i: nat) :
  ECCA_sub_type g (eUni (uType i)) (eUni (uType (S i)))
| aST_Pi (g: ECCAenv) (A1 A2 B1 B2: ECCAexp) (x1 x2: atom) :
  (ECCA_Equiv g A1 A2) ->
  (ECCA_sub_type (Assum g x1 A2) B1 (subst x2 (Id x1) B2)) -> (* eId x1 ?*)
  (ECCA_sub_type g (ePi x1 A1 B1) (ePi x2 A2 B2))
.

Hint Constructors ECCA_sub_type.

Inductive ECCA_has_type: ECCAenv -> ECCAexp -> ECCAexp -> Prop :=
| aT_Ax_Prop (g: ECCAenv) :
  (ECCA_has_type g (eUni uProp) (eUni (uType 0)))
| aT_Ax_Type (g: ECCAenv) (i: nat) :
  (ECCA_has_type g (eUni (uType i)) (eUni (uType (S i))))
| aT_Var (g: ECCAenv) (x: atom) (A: ECCAexp) :
  (ECCA_LookupTypeR g x A) -> (* this needs adjustment *)
  (ECCA_has_type g (eId x) A)
| aT_Bool (g: ECCAenv):
  (ECCA_has_type g (eBool) (Uni (uType 0)))
| aT_True (g: ECCAenv):
  (ECCA_has_type g (eTru) (eBool))
| aT_False (g: ECCAenv):
  (ECCA_has_type g (eFls) (eBool))
| aT_Sig (g: ECCAenv) (x: atom) (A B: ECCAexp) (i: nat) :
  (ECCA_has_type g A (eUni (uType i))) ->
  (ECCA_has_type (Assum g x A) B (eUni (uType i))) ->
  (ECCA_has_type g (eSig x A B) (eUni (uType i)))
| aT_Pair (g: ECCAenv) (v1 v2: ECCAexp) (A B: ECCAexp) (x: atom) :
  (ECCA_has_type g v1 A) ->
  (ECCA_has_type g v2 (subst x v1 B)) ->
  (ECCA_has_type g (ePair v1 v2 (eSig x A B)) (eSig x A B))
| aT_Prod_Prop (g: ECCAenv) (x: atom) (A B: ECCAexp) (i: nat):
  (ECCA_has_type g A (eUni (uType i))) ->
  (ECCA_has_type (Assum g x A) B (eUni (uProp))) ->
  (ECCA_has_type g (ePi x A B) (eUni (uProp)))
| aT_Prod_Type (g: ECCAenv) (x: atom) (A B: ECCAexp) (i: nat):
  (ECCA_has_type g A (eUni (uType i))) ->
  (ECCA_has_type (Assum g x A) B (eUni (uType i))) ->
  (ECCA_has_type g (ePi x A B) (eUni (uType i)))
| aT_Lam (g: ECCAenv) (x: atom) (A e B: ECCAexp) :
  (ECCA_has_type (Assum g x A) e B) ->
  (ECCA_has_type g (eAbs x A e) (ePi x A B))
(* ECCA_has_type: ECCAenv -> ECCAconf -> ECCAconf -> Prop := *)
| aT_Let (g: ECCAenv) (n: ECCAcomp) (m A B: ECCAexp) (x: atom):
  (ECCA_has_type g n A) ->
(*should this be (def(assum(g))) or (assum(def(g)))*)
  (ECCA_has_type (Def (Assum g x A) x n) m B) ->
  (ECCA_has_type g (eLet x n m) (subst x n B))
| aT_If (g: ECCAenv) (B U e1 e2: ECCAexp) (e: ECCAexp) (x: atom):
  ECCA_has_type (Assum g x eBool) B U -> 
  ECCA_has_type g e eBool ->
  ECCA_has_type (Eq g e Tru) e1 (subst x eTru B) ->
  ECCA_has_type (Eq g e Fls) e2 (subst x eFls B) -> 
  ECCA_has_type g (eIf e e1 e2) (subst x e B)
| aT_Conv (g: ECCAenv) (e A B U: ECCAexp) :
  (ECCA_has_type g e A) ->
  (ECCA_has_type g B U) ->
  (ECCA_sub_type g A B) ->
  (ECCA_has_type g e B)
(* ECCA_has_type: ECCAenv -> ECCAcomp -> ECCAconf -> Prop := *)
| aT_App (g: ECCAenv) (x: atom) (e e': ECCAexp) (A' B: ECCAexp) :
  (ECCA_has_type g e (ePi x A' B)) ->
  (ECCA_has_type g e' A') ->
  (ECCA_has_type g (eApp e e') (subst x e B))
| aT_Fst (g: ECCAenv) (e: ECCAexp) (A B: ECCAexp) (x: atom) :
  (ECCA_has_type g e (eSig x A B)) ->
  (ECCA_has_type g (eFst e) A)
| aT_Snd (g: ECCAenv) (e: ECCAexp) (A B: ECCAexp) (x: atom) :
  (ECCA_has_type g e (eSig x A B)) ->
  (ECCA_has_type g (eSnd e) (subst x (eFst e) B)) 
| aT_Subst (x: atom) (g: ECCAenv) (A B U: ECCAexp) (e e1 e2: ECCAexp):
  (ECCA_has_type (Assum g x A) B U) ->
  ECCA_has_type g e1 A -> 
  ECCA_has_type g e2 A ->
  ECCA_has_type g e (subst x e1 B) ->
  ECCA_LookupEqR g e1 e2 ->
  ECCA_has_type g (eSubst e1 e2 e) (subst x e2 B) 
.

Hint Constructors ECCA_has_type.

Goal ECCA_has_type Empty Bool (Uni (uType 0)).
Proof.
intros. apply aT_Bool. Qed.

Goal ECCA_has_type Empty (Pair Tru Bool (Sig 1 Bool (Uni (uType 0)))) (Sig 1 Bool (Uni (uType 0))).
Proof.
intros. apply aT_Pair. 
- apply aT_True.
- apply aT_Bool.
Qed.

Goal ECCA_has_type Empty (Snd (Pair Tru Bool (Sig 1 Bool (Uni (uType 0))))) (Uni (uType 0)).
Proof.
intros. eapply aT_Snd with (B:=(Uni (uType 0))). eauto. Qed.

Goal ECCA_has_type Empty (Fst (Pair Tru Bool (Sig 1 Bool (Uni (uType 0))))) (Bool).
Proof.
intros. eapply aT_Fst with (A:= Bool). eauto. Qed.



(* -=ECCA Notation=- *)

Bind Scope ECCA_scope with ECCAval.
Bind Scope ECCA_scope with ECCAconf.
Bind Scope ECCA_scope with ECCAcomp.
Bind Scope ECCA_scope with ECCAcont.
Delimit Scope ECCA_scope with ECCA.
Coercion Id: atom >-> ECCAval.
Definition natToAtom (i: nat) : atom := i.
Coercion natToAtom: nat >-> atom.

Definition F:=4.

Notation "'type' x" := (Uni (uType x)) (at level 50):  ECCA_scope.
Notation "'prop'" := (Uni uProp) (at level 50):  ECCA_scope.
Definition example_aType := (type 3)%ECCA: ECCAval.
Definition example_aProp := (prop)%ECCA: ECCAval.

Notation "{ e1 e2 }" := (App e1 e2) (at level 50,e1 at level 9):  ECCA_scope.
Definition example_aApp := { X Y }%ECCA: ECCAcomp.

Notation "'LET' x ':=' A 'in' B" := (Let x A B) (at level 50, format "'[v' 'LET'  x  ':='  A '/' 'in' '['  B ']' ']'") : ECCA_scope.
Definition example_aLet := (LET X := Y in Z)%ECCA : ECCAconf.
Print example_aLet.
(* Doesn't work because                                          V this is a conf, not a comp *)
(* Definition example_aLet2 := (LET X := (type 3) in LET F := (LET X := (type 2) in X) in ({X F}))%ECCA. *)
(* Print example_aLet2. *)

Notation "'P' x : A '->' B" := (Pi x A B) (at level 50, x at level 9, A at level 9) : ECCA_scope.
Definition example_aPi := (P X : Y -> Z)%ECCA : ECCAval.
Notation "'\' x : A '->' B" := (Abs x A B) (at level 50, x at level 9, A at level 9) : ECCA_scope.
Definition example_aAbs := (\ X : Y -> Z)%ECCA : ECCAval.

Notation "'[]'" := (Hole) (at level 50) : ECCA_scope.
Definition aHole := []%ECCA.
Notation "'LET' x ':=' '[]' 'in' B" := (LetHole x B) (at level 50) : ECCA_scope.
Definition example_aLetHole := (LET X := [] in X)%ECCA.
Print example_aLetHole.

Goal ECCA_has_type Empty (Fst (Pair Tru Fls 
    (Sig X Bool 
          (If X Bool (Pi Y Bool Bool))))) Bool.
Proof.
eapply aT_Fst with (A:= Bool). eapply aT_Pair.
  - apply aT_True.
  - cbv. apply aT_Conv with (A := Bool) (U := (Uni (uType 0))).
    + apply aT_False.
    + eapply aT_Conv.
      * apply aT_If with (e:= Tru) (e1:= Bool) (e2:= (P 1 : Bool -> Bool)%ECCA) (x:= 20) (B:= (Uni (uType 0))) (U:= Uni (uType 1)). 
        -- apply aT_Ax_Type.
        -- auto.
        -- auto.
        -- cbv. eapply aT_Prod_Type.
          ++ auto.
          ++ auto.
      * apply aT_Ax_Type.
      * cbn. apply aST_Cong. apply aE_EquivAlpha. apply aeq_id.
    + apply aST_Cong. apply aE_Equiv with (e:= eBool).
      * auto.
      * eauto.
Qed.
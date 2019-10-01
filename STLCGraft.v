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
Definition Y := (fresh  ( X:: nil) ).
Definition Z := (fresh (Y :: X :: nil)).

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

Lemma graft_id_size_preserving : forall xnew x' e, (ECCsize (graft x' (eId xnew) e)) = ECCsize e.
  intros. induction e. 
    - simpl. destruct (x' == x); auto.
    - auto.
    - simpl. destruct (x' == x).
      + cbn. rewrite -> IHe1. reflexivity.
      + cbn. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
    - cbn. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
Defined.


(* If there are free variables in the substitute,
   and if the term being substituted in binds one of them,
   then we need to perform an alpha conversion of the term being substituted in
   that avoids capturing any free variables in the substitute or in the body
   of the term being substituted in. *)

Unset Transparent Obligations.
Program Fixpoint trickySubst (x: atom) (arg body: ECCexp) (FVInArg: atoms) {measure (ECCsize body)}:=
match body with
  | eId x' => if (x == x') then arg else body
  | eAbs x' A e =>
      if (x == x')
        then (eAbs x' (trickySubst x arg A FVInArg) e)
        else let (xnew, _) := atom_fresh (FVInArg `union` (V e)) in
                    (eAbs xnew (trickySubst x arg A FVInArg) (trickySubst x arg (graft x' (eId xnew) e) FVInArg))
  | eApp e1 e2 => (eApp (trickySubst x arg e1 FVInArg) (trickySubst x arg e2 FVInArg))
  | eUni => body
end.
Solve Obligations with (Tactics.program_simpl; simpl; omega).
Solve Obligations with (Tactics.program_simpl; simpl; rewrite -> graft_id_size_preserving; omega).

Compute trickySubst X (eUni) (eId X) (FV eUni).
Eval cbn in trickySubst X (eUni) (eAbs Y (eUni) (eId X)) empty.
Compute subst x (eTru) (eAbs x (eId x) (eId x)).

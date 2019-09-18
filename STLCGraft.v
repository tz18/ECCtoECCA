(*Require Import Metalib.Metatheory.*)
Require Import Omega.
Require Import Coq.Lists.ListSet.
Require Import Coq.Program.Wf.

Open Scope list.

Parameter atom : Type.
Parameter atomeq_dec : forall x y : atom, {x = y} + {x <> y}.
Notation "a '==' b" := (atomeq_dec a b) (at level 10).

Definition atoms := set atom.
Definition empty : atoms := empty_set atom.
Definition singleton (x : atom) := x :: nil.

Definition union := set_union atomeq_dec.
Definition remove := set_remove atomeq_dec.
Definition add := set_add atomeq_dec.

Parameter fresh : atoms -> atom.


Inductive CCexp: Type :=
  | eId (x: atom)
  | eUni
  | eAbs (x: atom) (A e: CCexp)
  | eApp  (e1 e2: CCexp)
.

Fixpoint CCsize (e: CCexp) : nat :=
  match e with
  | eId _ => 1
  | eUni => 1
  | eAbs _ A e => 1 + (CCsize A) + (CCsize e)
  | eApp e1 e2 => 1 + (CCsize e1) + (CCsize e2)
end.

Hint Constructors CCexp.

Lemma CCsize_non_zero : forall e, 0 < CCsize e.
Proof.
  induction e; simpl; omega.
Qed.

(* -=CC Evaluation=- *)

Definition X := (fresh nil).
Definition Y := (fresh (X :: nil)).
Definition Z := (fresh (Y :: (X :: nil))).

(* Substitution *)
Fixpoint FV (e: CCexp) : atoms :=
match e with
  | eId x => singleton x
  | eUni => empty
  | eAbs x A e => union (FV A) (remove x (FV e))
  | eApp  e1 e2 => (union (FV e1) (FV e2))
end.

Fixpoint V (e: CCexp) : atoms :=
match e with
  | eId x => singleton x
  | eUni => empty
  | eAbs x A e => (add x (union (V A) (V e)))
  | eApp  e1 e2 => (union (V e1) (V e2))
end.

Fixpoint graft (x: atom) (arg body: CCexp) :=
match body with
  | eId x' => if (x == x') then arg else body
  | eAbs x' A e =>
      if (x == x')
        then (eAbs x' (graft x arg A) e)
        else (eAbs x' (graft x arg A) (graft x arg e))
  | eApp e1 e2 => (eApp (graft x arg e1) (graft x arg e2))
  | eUni => body
end.

Lemma graft_id_size_preserving : forall xnew x' e, (CCsize (graft x' (eId xnew) e)) = CCsize e.
  intros. induction e.
    - simpl. destruct (x' == x); auto.
    - auto.
    - simpl. destruct (x' == x).
      + cbn. rewrite -> IHe1. reflexivity.
      + cbn. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
    - cbn. rewrite -> IHe1. rewrite -> IHe2. reflexivity.
Defined.


Program Fixpoint Subst (x: atom) (arg body: CCexp) (FVInArg: atoms) {measure (CCsize body)}:=
match body with
  | eId x' => if (x == x') then arg else body
  | eAbs x' A e =>
      if (x == x')
        then (eAbs x' (Subst x arg A FVInArg) e)
        else let xnew := fresh (union (FVInArg) (V e)) in
                    (eAbs xnew (Subst x arg A FVInArg) (Subst x arg (graft x' (eId xnew) e) FVInArg))
  | eApp e1 e2 => (eApp (Subst x arg e1 FVInArg) (Subst x arg e2 FVInArg))
  | eUni => body
end.
Solve Obligations with (Tactics.program_simpl; simpl; omega).
Solve Obligations with (Tactics.program_simpl; simpl; rewrite -> graft_id_size_preserving; omega).

Compute Subst X (eUni) (eId X) (FV eUni).
Timeout 2 Compute Subst X (eUni) (eAbs Y (eUni) (eId X)) empty.

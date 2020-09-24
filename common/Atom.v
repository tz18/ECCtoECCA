Require Import SNames.Morph.
Require Export SNames.Var.
Require Export SNames.Context.

Definition atom {V: nat}:= @var V.

Inductive universe: Type :=
  | uProp
  | uType (i: nat)
.
Hint Constructors universe.
(* 

Definition X: atom := (fresh nil).
Definition Y: atom := (fresh (X :: nil)).
Definition Z: atom := (fresh (X :: Y :: nil)).

(* Notation " x == y " := (eq_dec x y) (at level 70). *)
Definition swap_var (x:atom) (y:atom) (z:atom) :=
  if (z == x) then y else if (z == y) then x else z.
 *)
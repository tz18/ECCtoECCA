Require Export Omega.
Require Export Coq.Lists.ListSet.
Require Export Coq.Init.Nat.
Require Export Coq.Arith.EqNat.
Require Export Arith.
Require Export Coq.Program.Wf.
Open Scope list.

Definition atom:= nat.
Definition atoms := set atom.
Definition empty : atoms := empty_set atom.
Definition singleton (x : atom) := x :: nil.

Definition union := set_union Nat.eq_dec.
Definition remove := set_remove Nat.eq_dec.
Definition add := set_add Nat.eq_dec.
Definition mem := set_mem Nat.eq_dec.

Definition fresh (ns: atoms): atom :=
(set_fold_left max ns 0) + 1
.

Definition X: atom := (fresh nil).
Definition Y: atom := (fresh (X :: nil)).
Definition Z: atom := (fresh (X :: Y :: nil)).

Inductive ECCuni: Type :=
  | uProp
  | uType (i: nat)
.

Definition swap_var (x:atom) (y:atom) (z:atom) :=
  if (z =? x) then y else if (z =? y) then x else z.

Require Import SNames.Morph.
Require Export SNames.Var.
Require Export SNames.Context.

Definition atom {V: nat}:= @var V.

Inductive universe: Type :=
  | uProp
  | uType (i: nat)
.
Hint Constructors universe.
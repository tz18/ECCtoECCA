Require Export typing.
Require Import core_lemmas.

(*===========================
  ==--Continuation Typing--==
  ===========================*)

(* TODO: incomplete *)

Inductive cont {V: nat}: Type :=
  | Hole
  | LetHole (B: @exp (S V))
.
Hint Constructors cont.
Bind Scope ECCA_scope with cont.

Inductive cont_r {V: nat}: Type :=
  | rHole
  | rLetHole (B: @conf (S V))
.
Hint Constructors cont_r.
Bind Scope ECCA_scope with cont_r.

Fixpoint unrestrict_cont {V: nat}(k: @cont_r V): @cont V:=
match k with
  | rHole => Hole
  | rLetHole B => LetHole (flattenconf B)
end.

Definition fill_hole {V: nat}(e: @exp V) (K: @cont V): @exp V:=
  match K with
    | Hole => e
    | LetHole B => eLet e B
end.
Notation "K '[' N ']'" := (fill_hole N K) (at level 200): ECCA_scope.

Definition fill_hole_r {V: nat}(e: @comp V) (K: @cont_r V): @conf V:=
  match K with
    | rHole => e
    | rLetHole B => Let e B
end.

Notation "'[]'" := (Hole) (at level 50) : ECCA_scope.
Notation "'LET' '_' ':=' '[]' 'in' B" := (LetHole B) (at level 50) : ECCA_scope.
Definition exId: @exp 1 := (eId (@bound 1 l0)).
Definition example_aLetHole := (LET _ := [] in (eId (@bound 1 l0)))%ECCA.
Definition ex_fillhole := (fill_hole (eTru) example_aLetHole).

Inductive cont_type {V: nat}: Type :=
  | Cont (M: @exp V) (A: @exp V) (B: @exp V)
.
Hint Constructors cont_type.
(* TODO: Add notation for cont type  *)

Inductive Types_cont : env -> cont  -> cont_type -> Prop :=
  | aK_Empty (M: exp) (g: env) (A: exp):
    Types g M A ->
    Types_cont g Hole (Cont M A A)
  | aK_Bind (g: env) (y: name) (M: exp) (M' A B: @exp 0):
    Types g M' A ->
    Types (ctx_cons g y (Def M' A)) (open y M) (open y (wk B)) ->
    Types_cont g (LetHole M) (Cont M' A B)
.

Hint Constructors Types_cont.

Lemma fill_with_hole_is_id {V: nat}(e: @exp V): fill_hole e Hole = e.
Proof.
eauto. Qed.

Definition wk_cont {V: nat} (k: @cont_r V): @cont_r (S V)
:=
match k with
| rHole => rHole
| rLetHole B => rLetHole (wk_conf B)
end.  

Definition close_cont {V: nat} (x: name) (k: @cont_r V): @cont_r (S V)
:=
match k with
| rHole => rHole
| rLetHole B => rLetHole (close_conf x B)
end.  

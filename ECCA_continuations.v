Require Export ECCA_typing.
Require Import ECCA_core_lemmas.

(*===========================
  ==--Continuation Typing--==
  ===========================*)

(* TODO: incomplete *)

Inductive cont {V: nat}: Type :=
  | Hole
  | LetHole (B: @ECCAexp (S V))
.
Hint Constructors cont.
Bind Scope ECCA_scope with cont.

Inductive cont_r {V: nat}: Type :=
  | rHole
  | rLetHole (B: @ECCAconf (S V))
.
Hint Constructors cont_r.
Bind Scope ECCA_scope with cont_r.

Fixpoint unrestrict_cont {V: nat}(k: @cont_r V): @cont V:=
match k with
  | rHole => Hole
  | rLetHole B => LetHole (flattenECCAconf B)
end.

Definition fill_hole {V: nat}(e: @ECCAexp V) (K: @cont V): @ECCAexp V:=
  match K with
    | Hole => e
    | LetHole B => eLet e B
end.
Notation "K '[' N ']'" := (fill_hole N K) (at level 200): ECCA_scope.

Definition fill_hole_r {V: nat}(e: @ECCAcomp V) (K: @cont_r V): @ECCAconf V:=
  match K with
    | rHole => e
    | rLetHole B => Let e B
end.

Notation "'[]'" := (Hole) (at level 50) : ECCA_scope.
Notation "'LET' '_' ':=' '[]' 'in' B" := (LetHole B) (at level 50) : ECCA_scope.
Definition exId: @ECCAexp 1 := (eId (@bound 1 l0)).
Definition example_aLetHole := (LET _ := [] in (eId (@bound 1 l0)))%ECCA.
Definition ex_fillhole := (fill_hole (eTru) example_aLetHole).

Inductive cont_type {V: nat}: Type :=
  | Cont (M: @ECCAexp V) (A: @ECCAexp V) (B: @ECCAexp V)
.
Hint Constructors cont_type.
(* TODO: Add notation for cont type  *)

Inductive ECCA_cont_has_type : ECCAenv -> cont  -> cont_type -> Prop :=
  | aK_Empty (M: ECCAexp) (g: ECCAenv) (A: ECCAexp):
    ECCA_has_type g M A ->
    ECCA_cont_has_type g Hole (Cont M A A)
  | aK_Bind (g: ECCAenv) (y: name) (M: ECCAexp) (M' A B: @ECCAexp 0):
    ECCA_has_type g M' A ->
    ECCA_has_type (ctx_cons g y (Def M' A)) (open y M) (open y (wk B)) ->
    ECCA_cont_has_type g (LetHole M) (Cont M' A B)
.

Hint Constructors ECCA_cont_has_type.

Lemma fill_with_hole_is_id {V: nat}(e: @ECCAexp V): fill_hole e Hole = e.
Proof.
eauto. Qed.

Definition wk_cont {V: nat} (k: @cont_r V): @cont_r (S V)
:=
match k with
| rHole => rHole
| rLetHole B => rLetHole (wk_conf B)
end.  

Require Export ECCA_typing.

(*===========================
  ==--Continuation Typing--==
  ===========================*)

(* TODO: incomplete *)

Inductive cont: Type :=
  | Hole
  | LetHole (E: @ECCAexp 1)
.
Hint Constructors cont.
Bind Scope ECCA_scope with cont.

Inductive cont_r: Type :=
  | rHole
  | rLetHole (E: @ECCAconf 1)
.
Hint Constructors cont_r.
Bind Scope ECCA_scope with cont_r.

Fixpoint unrestrict_cont (k: cont_r):=
match k with
  | rHole => Hole
  | rLetHole E => LetHole (flattenECCAconf E)
end.

Definition fill_hole (e: ECCAexp) (K: cont): ECCAexp :=
  match K with
    | Hole => e
    | LetHole B => eLet e B
end.
Notation "K '[' N ']'" := (fill_hole N K) (at level 200): ECCA_scope.

Definition fill_hole_r (e: ECCAcomp) (K: cont_r): @ECCAconf 0 :=
  match K with
    | rHole => e
    | rLetHole B => Let e B
end.

Notation "'[]'" := (Hole) (at level 50) : ECCA_scope.
Definition aHole := []%ECCA.
Notation "'LET' '_' ':=' '[]' 'in' B" := (LetHole B) (at level 50) : ECCA_scope.
Definition exId: @ECCAexp 1 := (eId (@bound 1 l0)).
Definition example_aLetHole := (LET _ := [] in (eId (@bound 1 l0)))%ECCA.
Definition ex_fillhole := (fill_hole (eTru) example_aLetHole).

Inductive cont_type: Type :=
  | Cont (M: @ECCAexp 0) (A: @ECCAexp 0) (B: @ECCAexp 0)
.
Hint Constructors cont_type.
(* TODO: Add notation for cont type  *)

Inductive ECCA_cont_has_type: ECCAenv -> cont -> cont_type -> Prop :=
  | aK_Empty (M: ECCAexp) (g: ECCAenv) (A: ECCAexp):
    ECCA_cont_has_type g Hole (Cont M A A)
  | aK_Bind (g: ECCAenv) (y: name) (M: ECCAexp) (M' A B: ECCAexp):
    ECCA_has_type g M' A ->
    ECCA_has_type (g & y ~ Def A M') (open y M) B ->
    ECCA_cont_has_type g (LetHole M) (Cont M' A B)
.

Hint Constructors ECCA_cont_has_type.

Lemma fill_with_hole_is_id (e: ECCAexp): fill_hole e Hole = e.
Proof.
eauto. Qed.

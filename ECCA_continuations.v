Require Export ECCA_typing.

(*===========================
  ==--Continuation Typing--==
  ===========================*)

(* TODO: incomplete *)

Inductive cont: Type :=
  | Hole
  | LetHole (x: atom) (E: ECCAexp)
.
Hint Constructors cont.
Bind Scope ECCA_scope with cont.

Inductive cont_r: Type :=
  | rHole
  | rLetHole (x: atom) (E: ECCAconf)
.
Hint Constructors cont_r.
Bind Scope ECCA_scope with cont_r.

Fixpoint unrestrict_cont (k: cont_r):=
match k with
  | rHole => Hole
  | rLetHole x E => LetHole x (flattenECCAconf E)
end.

Definition fill_hole (e: ECCAexp) (K: cont): ECCAexp :=
  match K with
    | Hole => e
    | LetHole x B => eLet x e B
end.

Definition fill_hole_r (e: ECCAcomp) (K: cont_r): ECCAconf :=
  match K with
    | rHole => e
    | rLetHole x B => Let x e B
end.

Notation "'[]'" := (Hole) (at level 50) : ECCA_scope.
Definition aHole := []%ECCA.
Notation "'LET' x ':=' '[]' 'in' B" := (LetHole x B) (at level 50) : ECCA_scope.
Definition example_aLetHole := (LET X := [] in (eId X))%ECCA.

Inductive cont_type: Type :=
  | Cont (M: ECCAexp) (A: ECCAexp) (B: ECCAexp)
.
Hint Constructors cont_type.
(* TODO: Add notation for cont type  *)

Inductive ECCA_cont_has_type: ECCAenv -> cont -> cont_type -> Prop :=
  | aK_Empty (M: ECCAexp) (g: ECCAenv) (A: ECCAexp):
    ECCA_cont_has_type g Hole (Cont M A A)
  | aK_Bind (g: ECCAenv) (y: atom) (M: ECCAexp) (M' A B: ECCAexp):
    ECCA_has_type g M' A ->
    ECCA_has_type (Assum (Def g y M') y A) M B ->
    y `notin` FV B ->  (*Prove as a lemma later*)
    ECCA_cont_has_type g (LetHole y M) (Cont M' A B)
.

Hint Constructors ECCA_cont_has_type.

Lemma fill_with_hole_is_id (e: ECCAexp): fill_hole e Hole = e.
Proof.
eauto. Qed.

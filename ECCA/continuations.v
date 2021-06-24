Require Export typing.
Require Import core_lemmas.

(*===========================
  ==--Continuation Typing--==
  ===========================*)

(* TODO: incomplete *)

Inductive cont: Type :=
  | Hole
  | LetHole (B: @exp (S 0))
.
Hint Constructors cont.
Bind Scope ECCA_scope with cont.
Notation "'[]'" := (Hole) (at level 200): ECCA_scope.

Definition cont_is_ANF (k: cont): Prop :=
match k with
| Hole => True
| LetHole B => isConf B
end.

Bind Scope ECCA_scope with cont_is_ANF.
Notation "'[]'" := (Hole) (at level 200): ECCA_scope.

Definition fill_hole (e: exp) (K: cont): exp:=
  match K with
    | Hole => e
    | LetHole B => eLet e B
end.
Check fill_hole.
Notation "'(' K ')' '[' N ']'" := (fill_hole N K) (at level 300): ECCA_scope.
Notation "'LET' '_' ':=' '[]' 'in' B" := (LetHole B) (at level 50) : ECCA_scope.

Definition exId: @exp 1 := (eId (@bound 1 l0)).
Definition example_aLetHole := (LET _ := [] in (eId (@bound 1 l0)))%ECCA.
Definition ex_fillhole := (fill_hole (eTru) example_aLetHole).
Eval cbn in ex_fillhole.

Inductive cont_type : Type :=
  | Cont (M A B: @exp 0)
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

Lemma fill_with_hole_is_id {V: nat}(e: exp): fill_hole e Hole = e.
Proof.
eauto. Qed.

(*Definition wk_cont {V: nat} (k: cont_r): @cont_r (S V)
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
*)
Require Import Program.
Require Import Lia.
Require Import Recdef.

Definition shift_cont (x: name) (K: cont):=
match K with
  | Hole => Hole
  | LetHole B => LetHole (open x (wk B))
end.

Check Let.
Import String.
Open Scope string.

Function het_compose (K : cont) (M : exp) {measure esize M}: exp :=
  match M with
  | eId _ => fill_hole M K
  | eUni _ => fill_hole M K
  | ePi _ _ => fill_hole M K
  | eAbs _ _ => fill_hole M K
  | eSig _ _ => fill_hole M K
  | ePair _ _ _ => fill_hole M K
  | eTru => fill_hole M K
  | eFls => fill_hole M K
  | eBool => fill_hole M K
  | eLet N M' => eLet N (close "k" (het_compose (shift_cont "k" K) (open "k" M')))
  | eIf v M1 M2 => eIf v (het_compose K M1) (het_compose K M2)
  | eApp _ _ => fill_hole M K
  | eFst _ => fill_hole M K
  | eSnd _ => fill_hole M K
  end.
Proof.
+ intros. cbn.
rewrite esize_open_id. cbn. lia.
+ intros. cbn. lia.
+ intros. cbn. lia.
Qed.
Hint Rewrite het_compose_equation.
Check het_compose.

Notation "'(' K ')' '<<' M '>>'" := (het_compose K M) (at level 250): ECCA_scope.

Definition cont_compose (K : cont) (K' : cont) : cont:=
  match K' with
  | Hole => K
  | LetHole M => LetHole (close "k" (het_compose (shift_cont "k" K) (open "k" M)))
  end.

Notation "'(' K1 ')' '<<<' K2 '>>>'" := (cont_compose K1 K2) (at level 250): ECCA_scope.
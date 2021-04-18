Require Import core.

(*
=====================================
=============--Size--================
=====================================
*)
Require Import Lia.
Require Import String Morph Var Context Relative.

Lemma esize_non_zero : forall V e, 0 < @esize V e.
Proof.
  induction e; simpl; lia.
Qed.

Lemma esize_open_id : forall {V: nat} (e: @exp (1 + V)) x, @esize (V) (open x e) = @esize (1 + V) e.
Proof. intros. 
  inductT e; induction V0; cbn; try easy; try (rewrite IHe1; try easy; rewrite IHe2; try easy; try (rewrite IHe3; try easy)).
  all: ( rewrite IHe; try easy).
Qed.

Lemma esize_close_id : forall {V: nat} (e: @exp (V)) x, @esize (1 + V) (close x e) = @esize (V) e.
Proof. intros. induction e; names; auto.
Qed.

Lemma esize_wk_id : forall {V: nat} (e: @exp (V)), @esize (1 + V) (wk e) = @esize (V) e.
Proof. intros. induction e; names; auto.
Qed.

Hint Resolve esize_open_id esize_close_id esize_wk_id.

(*
================================
========== Names ===============
================================
*)


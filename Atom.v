Require Export Omega.
Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Inductive ECCuni: Type :=
  | uProp
  | uType (i: nat)
.

Definition X: atom := (fresh nil).
Definition Y: atom := (fresh (X :: nil)).
Definition Z: atom := (fresh (X :: Y :: nil)).

(* Notation " x == y " := (eq_dec x y) (at level 70).
 *)
Definition swap_var (x:atom) (y:atom) (z:atom) :=
  if (z == x) then y else if (z == y) then x else z.

(* 
Definition atom:= nat.
Definition atoms := set atom.
Definition empty : atoms := empty_set atom.

Definition eq_dec : forall n m : atom, {n = m} + {n <> m} := Nat.eq_dec.
Definition union := set_union eq_dec.
Definition remove := set_remove eq_dec.
Definition add := set_add eq_dec.
Definition mem := set_mem eq_dec.

Definition fresh (ns: atoms): atom :=
(set_fold_left max ns 0) + 1
.






Definition fresh_in (x: atom) (N: atoms) :=
  ~ (set_In x N).

Lemma fresh_is_fresh (ns: atoms): fresh_in (fresh ns) ns.
Proof.
induction ns.
- cbv. auto.
- cbn. unfold fresh_in. unfold set_In. unfold List.In. unfold not. intros. destruct H.
  + unfold set_fold_left.
  +

Lemma fresh_over_union (x: atom) (N1 N2: atoms):
fresh_in x (union N1 N2) ->
fresh_in x N1 /\ fresh_in x N2.
Proof.
intros. unfold fresh_in. unfold fresh_in in H. split.
- unfold set_In. unfold set_In in H. pose proof (set_union_iff eq_dec x N1 N2) as s. rewrite -> s in H. auto.
- unfold set_In. unfold set_In in H. pose proof (set_union_iff eq_dec x N1 N2) as s. rewrite -> s in H. auto.
Qed. *)
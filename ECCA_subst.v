Require Export ECCA_core.


(* 
=====================================
=======--Substitition--==============
=====================================
*)

Fixpoint FV (e: ECCAexp) : atoms :=
match e with
  | eId x => singleton x
  | eUni U => empty
  | ePi x A B =>  union (FV A) (remove x (FV B))
  | eAbs x A e => union (FV A) (remove  x (FV e))
  | eApp  e1 e2 => (union (FV e1) (FV e2))
  | eLet x e1 e2 => union (FV e1) (remove  x (FV e2))
  | eSig x A B => (union (FV A) (remove  x (FV B)))
  | ePair e1 e2 A => (union (union  (FV e1) (FV e2)) (FV A))
  | eFst e => (FV e)
  | eSnd e => (FV e)
(*   | eIf e e1 e2 => (union (union  (FV e) (FV e1)) (FV e2)) *)
  | _ => empty
end.

(*Let's get nominal!*)

Fixpoint swap (x:atom) (y:atom) (t:ECCAexp) : ECCAexp :=
  match t with
  | eId z     => eId (swap_var x y z)
  | eAbs z A t1  => eAbs (swap_var x y z) (swap x y A) (swap x y t1)
  | eApp t1 t2 => eApp (swap x y t1) (swap x y t2)
  | ePi x' A B => ePi (swap_var x y x') (swap x y A) (swap x y B)
  | eLet x' e1 e2 => eLet (swap_var x y x') (swap x y e1) (swap x y e2)
  | eSig x' A B => eSig (swap_var x y x') (swap x y A) (swap x y B)
  | ePair e1 e2 A => ePair (swap x y e1) (swap x y e2) (swap x y A)
  | eFst e => (eFst (swap x y e))
  | eSnd e => (eSnd (swap x y e))
(*   | eIf e e1 e2 => (eIf (swap x y e) (swap x y e1) (swap x y e2)) *)
  | _ => t
  end.

Fixpoint ECCAsize (e: ECCAexp) : nat :=
  match e with
  | eId _ => 1
  | eUni _ => 1
  | ePi _ A B => 1 + (ECCAsize A) + (ECCAsize B)
  | eAbs _ A e => 1 + (ECCAsize A) + (ECCAsize e)
  | eApp e1 e2 => 1 + (ECCAsize e1) + (ECCAsize e2)
  | eLet _ e1 e2 => 1 + (ECCAsize e1) + (ECCAsize e2)
  | eSig _ A B => 1 + (ECCAsize A) + (ECCAsize B)
  | ePair e1 e2 A => 1 + (ECCAsize e1) + (ECCAsize e2) + (ECCAsize A)
  | eFst e => 1 + (ECCAsize e)
  | eSnd e => 1 + (ECCAsize e)
(*   | eIf e e1 e2 => 1 + (ECCAsize e) + (ECCAsize e1) + (ECCAsize e2) *)
(*   | eSubst a b c => 1 + (ECCAsize a) + (ECCAsize b) + (ECCAsize c) *)
  | _ => 1
end.

Lemma ECCAsize_non_zero : forall e, 0 < ECCAsize e.
Proof.
  induction e; simpl; omega.
Qed.

Lemma swap_size_eq : forall x y t,
    ECCAsize (swap x y t) = ECCAsize t.
Proof.
  induction t; simpl; auto.
Qed.

(* If there are free variables in the substitute,
   and if the term being substituted in binds one of them,
   then we need to perform an alpha conversion of the term being substituted in
   that avoids capturing any free variables in the substitute or in the body
   of the term being substituted in. *)
Require Import Recdef.

Function substWork (x: atom) (arg body: ECCAexp) {measure ECCAsize body}:=
if (AtomSetImpl.mem x (FV body)) then 
  match body with
    | eId x' => if (x == x') then arg else body
    | eAbs x' A e =>
        if (x == x')
          then (eAbs x' (substWork x arg A) e)
          else let (xnew,_) := atom_fresh (union (FV arg) (FV e)) in
                      (eAbs xnew (substWork x arg A) (substWork x arg (swap x' xnew e)))
    | ePi x' A B =>
        if (x == x')
          then (ePi x' (substWork x arg A) B)
          else let (xnew,_) := atom_fresh (union (FV arg) (FV B)) in
                  (ePi xnew (substWork x arg A) (substWork x arg (swap x' xnew B)))
    | eLet x' A B =>
        if (x == x')
          then (eLet x' (substWork x arg A) B)
          else let (xnew,_) := atom_fresh (union (FV arg) (FV B)) in
                  (eLet xnew (substWork x arg A) (substWork x arg (swap x' xnew B)))
    | eSig x' A B =>
        if (x == x')
          then (eSig x' (substWork x arg A) B)
          else let (xnew,_) := atom_fresh (union (FV arg) (FV B)) in
                  (eSig xnew (substWork x arg A) (substWork x arg (swap x' xnew B)))
    | eApp e1 e2 => (eApp (substWork x arg e1) (substWork x arg e2))
    | ePair e1 e2 A => (ePair (substWork x arg e1) (substWork x arg e2) (substWork x arg A))
    | eFst e => (eFst (substWork x arg e))
    | eSnd e => (eSnd (substWork x arg e))
  (*   | eIf e e1 e2 => (eIf (substWork x arg e FVInArg) (substWork x arg e1 FVInArg) (substWork x arg e2 FVInArg)) *)
    | _ => body
  (*   | eSubst a b c => eSubst (substWork x arg a FVInArg) (substWork x arg b FVInArg) (substWork x arg c FVInArg) (**) *)
  end
else body.
Proof.
1-19: try (Tactics.program_simpl; cbn; omega).
1-4: try (Tactics.program_simpl; cbn; rewrite -> swap_size_eq; omega).
Qed.

Definition subst (x: atom) (arg body: ECCAexp):= substWork x arg body.
Search "substWork_eq".

Notation "b '[' a '/' x ']'":= (subst x a b) (at level 50, a at level 50): ECCA_scope. 
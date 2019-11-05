
(*From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Init.Datatypes.*)
Require Import Omega.
Require Import Coq.Lists.ListSet.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.EqNat.
Require Import Arith.
Require Import Coq.Program.Wf.
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


(* Module ECC. *)

(* -=ECC Definition=- *)

Inductive ECCuni: Type :=
  | uProp
  | uType (i: nat)
.

Inductive ECCexp: Type :=
  | eId (x: atom)
  | eUni (U: ECCuni)
  | ePi (x: atom) (A B: ECCexp)
  | eAbs (x: atom) (A e: ECCexp)
  | eApp  (e1 e2: ECCexp)
  | eLet (x: atom) (e1 e2: ECCexp)
  | eSig (x: atom) (A B: ECCexp)
  | ePair (e1 e2 A: ECCexp)
  | eFst (e: ECCexp)
  | eSnd (e: ECCexp)
  | eIf (e e1 e2: ECCexp)
  | eTru
  | eFls
  | eBool
.

Inductive ECCenv: Type :=
  | gEmpty
  | gAssum (g: ECCenv) (x: atom) (A: ECCexp)
  | gDef (g: ECCenv) (x: atom) (e: ECCexp)
.

Fixpoint ECCsize (e: ECCexp) : nat :=
  match e with
  | eId _ => 1
  | eUni _ => 1
  | ePi _ A B => 1 + (ECCsize A) + (ECCsize B)
  | eAbs _ A e => 1 + (ECCsize A) + (ECCsize e)
  | eApp e1 e2 => 1 + (ECCsize e1) + (ECCsize e2)
  | eLet _ e1 e2 => 1 + (ECCsize e1) + (ECCsize e2)
  | eSig _ A B => 1 + (ECCsize A) + (ECCsize B)
  | ePair e1 e2 A => 1 + (ECCsize e1) + (ECCsize e2) + (ECCsize A)
  | eFst e => 1 + (ECCsize e)
  | eSnd e => 1 + (ECCsize e)
  | eIf e e1 e2 => 1 + (ECCsize e) + (ECCsize e1) + (ECCsize e2)
  | eTru => 1
  | eFls => 1
  | eBool => 1
end.

Hint Constructors ECCuni.
Hint Constructors ECCexp.
Hint Constructors ECCenv.

Lemma ECCsize_non_zero : forall e, 0 < ECCsize e.
Proof.
  induction e; simpl; omega.
Qed.

(* -=ECC Evaluation=- *)

(* -Lookup- *)

Inductive ECC_LookupTypeR : ECCenv -> atom -> ECCexp -> Prop:=
  | LT_gFirst (g': ECCenv) (x: atom) (A: ECCexp):
    ECC_LookupTypeR (gAssum g' x A) x A
  | LT_AssumRest (g: ECCenv) (x x': atom) (A a': ECCexp):
    ECC_LookupTypeR g x A ->
    (x <> x') ->
    (ECC_LookupTypeR (gAssum g x' a') x A)
  | LT_DefRest (g: ECCenv) (x x': atom) (A a': ECCexp):
    ECC_LookupTypeR g x A ->
(*     (x <> x') -> *)
    (ECC_LookupTypeR (gDef g x' a') x A)
.

Inductive ECC_LookupDefR : ECCenv -> atom -> ECCexp -> Prop:=
  | LD_gFirst (g': ECCenv) (x: atom) (e A: ECCexp):
    ECC_LookupDefR (gAssum (gDef g' x e) x A) x e
  | LD_AssumRest (g: ECCenv) (x x': atom) (e a': ECCexp):
    ECC_LookupDefR g x e ->
    (x <> x') ->
    (ECC_LookupDefR (gAssum g x' a') x e)
  | LD_DefRest (g: ECCenv) (x x': atom) (e e': ECCexp):
    ECC_LookupDefR g x e ->
    (x <> x') ->
    (ECC_LookupDefR (gDef g x' e') x e)
.
(* Q: what if looking up a type and get a value first, or vice versa? *)

Hint Constructors ECC_LookupTypeR.

Example ECC_LookupFirstExample:
ECC_LookupTypeR (gAssum gEmpty X eTru) X eTru.
Proof.
  auto.
Qed.

Example ECC_LookupRestExample:
X <> Y -> ECC_LookupTypeR (gAssum (gAssum gEmpty X eTru) Y eFls) X eTru.
Proof.
  auto.  (* WOW!*)
Qed.

Fixpoint ECC_LookupType (g: ECCenv) (x: atom): option ECCexp :=
match g with
  | gEmpty => None
  | gAssum g' x' A => if (x' =? x) then Some A else (ECC_LookupType g' x)
  | gDef g' x' e => (ECC_LookupType g' x)
end.

Fixpoint ECC_LookupDef (g: ECCenv) (x: atom): option ECCexp :=
match g with
  | gEmpty => None
  | gAssum g' x' A => if (x' =? x) then match g' with
      | gEmpty => None
      | gAssum g'' x'' A => None
      | gDef g' x'' e => if (x'' =? x) then Some e else None
      end      
      else (ECC_LookupDef g' x)
  | gDef g' x' e => if (x' =? x) then None else (ECC_LookupDef g' x)
end.

Lemma ECC_EmptyImpliesNothing : forall (x: atom) (A: ECCexp), ECC_LookupTypeR gEmpty x A -> False.
Proof.
intros. inversion H.
Qed.

Lemma ECC_LookupTypeReflects (g: ECCenv) (x: atom) (A: ECCexp) : ECC_LookupTypeR g x A <-> (ECC_LookupType g x) = Some A.
Proof.
intros. split.
 - intros. induction H.
  + cbn. rewrite <- beq_nat_refl. reflexivity.
  + cbn. cut (x' =? x = false).
    * intros. rewrite H1. apply IHECC_LookupTypeR.
    * apply Nat.eqb_neq. auto.
  + cbn. apply IHECC_LookupTypeR.
 - intros. induction g.
  + discriminate.
  + inversion H. destruct (x0 =? x) eqn:eq.
    * inversion H1. apply Nat.eqb_eq in eq. rewrite eq. apply LT_gFirst.
    * apply LT_AssumRest.
      -- apply IHg. apply H1.
      -- apply Nat.eqb_neq in eq. auto.
  + apply LT_DefRest.
    * apply IHg. apply H.
Qed.

Lemma ECC_LookupDefReflects (g: ECCenv) (x: atom) (A: ECCexp) : ECC_LookupDefR g x A <-> (ECC_LookupDef g x) = Some A.
Proof.
intros. split.
 - intros. induction H.
  + cbn. rewrite <- beq_nat_refl. reflexivity.
  + cbn. cut (x' =? x = false).
    * intros. rewrite H1. apply IHECC_LookupDefR.
    * apply Nat.eqb_neq. auto.
  + cbn. cut (x' =? x = false). 
    * intros. rewrite H1. apply IHECC_LookupDefR.
    * apply Nat.eqb_neq. auto.
 - intros. induction g.
  + discriminate.
  + inversion H. destruct (x0 =? x) eqn:eq.
    *  destruct g eqn:eq2.
      -- discriminate.
      -- discriminate.
      -- apply Nat.eqb_eq in eq. rewrite eq. destruct (x1 =? x) eqn:eq3.
        ++ inversion H1. apply Nat.eqb_eq in eq3. rewrite eq3. apply LD_gFirst.
        ++ discriminate.
   * apply LD_AssumRest.
     -- apply IHg. apply H1.
     -- apply Nat.eqb_neq in eq. auto.
  + inversion H. destruct (x0 =? x) eqn:eq.
    * discriminate.
    * apply LD_DefRest.
      -- apply IHg. apply H1.
      -- apply Nat.eqb_neq in eq. auto.
Qed.

(* Substitution *)


Fixpoint FV (e: ECCexp) : atoms :=
match e with
  | eId x => singleton x
  | eUni U => empty
  | ePi x A B =>  union (FV A) (remove x (FV B))
  | eAbs x A e => union (FV A) (remove  x (FV e))
  | eApp  e1 e2 => (union (FV e1) (FV e2))
  | eLet x e1 e2 => (union (FV e1) (FV e2))
  | eSig x A B => (union (FV A) (remove  x (FV B)))
  | ePair e1 e2 A => (union (union  (FV e1) (FV e2)) (FV A))
  | eFst e => (FV e)
  | eSnd e => (FV e)
  | eIf e e1 e2 => (union (union  (FV e) (FV e1)) (FV e2))
  | eTru => empty
  | eFls => empty
  | eBool => empty
end.

(*Let's get nominal!*)

Definition swap_var (x:atom) (y:atom) (z:atom) :=
  if (z =? x) then y else if (z =? y) then x else z.

Fixpoint swap (x:atom) (y:atom) (t:ECCexp) : ECCexp :=
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
  | eIf e e1 e2 => (eIf (swap x y e) (swap x y e1) (swap x y e2))
  | _ => t
  end.

Lemma swap_size_eq : forall x y t,
    ECCsize (swap x y t) = ECCsize t.
Proof.
  induction t; simpl; auto.
Qed.


(* If there are free variables in the substitute,
   and if the term being substituted in binds one of them,
   then we need to perform an alpha conversion of the term being substituted in
   that avoids capturing any free variables in the substitute or in the body
   of the term being substituted in. *)

Program Fixpoint substWork (x: atom) (arg body: ECCexp) (FVInArg: atoms) {measure (ECCsize body)}:=
match body with
  | eId x' => if (x =? x') then arg else body
  | eAbs x' A e =>
      if (x =? x')
        then (eAbs x' (substWork x arg A FVInArg) e)
        else let xnew := fresh (union FVInArg (FV e)) in
                    (eAbs xnew (substWork x arg A FVInArg) (substWork x arg (swap x' xnew e) FVInArg))
  | ePi x' A B =>
      if (x =? x')
        then (ePi x' (substWork x arg A FVInArg) B)
        else let xnew := fresh (union FVInArg (FV B)) in
                (ePi xnew (substWork x arg A FVInArg) (substWork x arg (swap x' xnew B) FVInArg))
  | eLet x' A B =>
      if (x =? x')
        then (eLet x' (substWork x arg A FVInArg) B)
        else let xnew := fresh (union FVInArg (FV B)) in
                (eLet xnew (substWork x arg A FVInArg) (substWork x arg (swap x' xnew B) FVInArg))
  | eSig x' A B =>
      if (x =? x')
        then (eSig x' (substWork x arg A FVInArg) B)
        else let xnew := fresh (union FVInArg (FV B)) in
                (eSig xnew (substWork x arg A FVInArg) (substWork x arg (swap x' xnew B) FVInArg))
  | eApp e1 e2 => (eApp (substWork x arg e1 FVInArg) (substWork x arg e2 FVInArg))
  | eUni U => body
  | ePair e1 e2 A => (ePair (substWork x arg e1 FVInArg) (substWork x arg e2 FVInArg) (substWork x arg A FVInArg))
  | eFst e => (eFst (substWork x arg e FVInArg))
  | eSnd e => (eSnd (substWork x arg e FVInArg))
  | eIf e e1 e2 => (eIf (substWork x arg e FVInArg) (substWork x arg e1 FVInArg) (substWork x arg e2 FVInArg))
  | eTru => eTru
  | eFls => eFls
  | eBool => eBool
end.
Obligations.
Solve Obligations with (Tactics.program_simpl; cbn; omega).
Solve Obligations with (Tactics.program_simpl; cbn; rewrite -> swap_size_eq; omega).

Definition subst (x: atom) (arg body: ECCexp):= substWork x arg body (FV arg).

Inductive ECC_Aeq : ECCexp -> ECCexp -> Prop :=
  | aeq_id (e: ECCexp):
    ECC_Aeq e e
  | aeq_var (x: atom):
     ECC_Aeq (eId x) (eId x)
  | aeq_abs_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (eAbs x t1 b1) (eAbs x t2 b2)
  | aeq_abs_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (eAbs x t1 b1) (eAbs y t2 b2)
  | aeq_pi_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (ePi x t1 b1) (ePi x t2 b2)
  | aeq_pi_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (ePi x t1 b1) (ePi y t2 b2)
  | aeq_let_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (eLet x t1 b1) (eLet x t2 b2)
  | aeq_let_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (eLet x t1 b1) (eLet y t2 b2)
  | aeq_sig_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (eSig x t1 b1) (eSig x t2 b2)
  | aeq_sig_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (eSig x t1 b1) (eSig y t2 b2)
  | aeq_app (t1 t2 t1' t2': ECCexp):
     ECC_Aeq t1 t1' -> ECC_Aeq t2 t2' ->
     ECC_Aeq (eApp t1 t2) (eApp t1' t2')
  | aeq_pair (t1 t2 t1' t2' A A': ECCexp):
     ECC_Aeq t1 t1' -> ECC_Aeq t2 t2' ->
     ECC_Aeq A A' ->
     ECC_Aeq (ePair t1 t2 A) (ePair t1' t2' A')
  | aeq_eFst (e e': ECCexp):
     ECC_Aeq e e' ->
     ECC_Aeq (eFst e) (eFst e')
  | aeq_eSnd (e e': ECCexp):
     ECC_Aeq e e' ->
     ECC_Aeq (eSnd e) (eSnd e')
  | aeq_if (e1 e2 e3 e1' e2' e3': ECCexp):
     ECC_Aeq e1 e1' ->
     ECC_Aeq e2 e2' ->
     ECC_Aeq e3 e3' ->
     ECC_Aeq (eIf e1 e2 e3) (eIf e1' e2' e3').

Hint Constructors ECC_Aeq.

Timeout 30 Compute substWork X (eTru) (eId X) (FV eTru). 
Compute substWork X (eTru) (eAbs Y (eBool) (eId X)) (FV eTru).
Compute substWork X (eTru) (eAbs X (eId X) (eId X)) (FV eTru).
Eval vm_compute in substWork X (eTru) (eAbs X (eId X) (eId X)) (FV eTru).


(* -Step- *)
Inductive ECC_RedR : ECCenv -> ECCexp -> ECCexp -> Prop :=
  | R_ID (g: ECCenv) (x: atom) (e': ECCexp) :
    ECC_LookupDefR g x e' -> ECC_RedR g (eId x) e'
  | R_App (g: ECCenv) (x: atom) (A body arg: ECCexp) :
    ECC_RedR g (eApp (eAbs x A body) arg) (subst x arg body) (*do anything with env here?*)
  | R_Fst (g: ECCenv) (e1 e2 A: ECCexp) :
    ECC_RedR g (eFst (ePair e1 e2 A)) e1
  | R_Snd (g: ECCenv) (e1 e2 A: ECCexp) :
    ECC_RedR g (eSnd (ePair e1 e2 A)) e2
  | R_Let (g: ECCenv) (x: atom) (e1 e2: ECCexp) :
    ECC_RedR g (eLet x e1 e2) (subst x e1 e2)  (*or here?*)
  | R_IfTru (g: ECCenv) (e1 e2: ECCexp) :
    ECC_RedR g (eIf eTru e1 e2) e1
  | R_IfFls (g: ECCenv) (e1 e2: ECCexp) :
    ECC_RedR g (eIf eFls e1 e2) e2
.

Hint Constructors ECC_RedR.

(* Reflective Transitive Closure of step*)
Inductive ECC_RedClosR : ECCenv -> ECCexp -> ECCexp -> Prop :=
  (*| R_RedR (g g': ECCenv) (e e': ECCexp): (* maybe don't need this one? it follows from refl + trans*)
      ECC_RedR g e e' ->
      ECC_RedClosR g e e'*)
  | R_Refl (g: ECCenv) (e: ECCexp):
      ECC_RedClosR g e e
  | R_Trans (g: ECCenv) (e e' e'': ECCexp) :
      ECC_RedR g e e' ->
      ECC_RedClosR g e' e'' ->
      ECC_RedClosR g e e''
  | R_CongLet (g: ECCenv) (e e1 e2: ECCexp) (x: atom) :
      ECC_RedClosR (gDef g x e) e1 e2 ->
      ECC_RedClosR g (eLet x e e1) (eLet x e e2)
  | R_CongLam1 (g: ECCenv) (A A' e e': ECCexp) (x: atom) :
      ECC_RedClosR g A A' ->
      ECC_RedClosR (gAssum g x A) e e' ->
      ECC_RedClosR g (eAbs x A e) (eAbs x A' e')
  | R_CongPi (g: ECCenv) (A A' B B': ECCexp) (x: atom) :
      ECC_RedClosR g A A' ->
      ECC_RedClosR (gAssum g x A) B B' ->
      ECC_RedClosR g (ePi x A B) (ePi x A' B')
  | R_CongSig (g: ECCenv) (A A' B B': ECCexp) (x: atom) :
      ECC_RedClosR g A A' ->
      ECC_RedClosR (gAssum g x A) B B' ->
      ECC_RedClosR g (eSig x A B) (eSig x A' B')
  | R_CongPair (g: ECCenv) (e1 e1' e2 e2' A A': ECCexp) :
      ECC_RedClosR g e1 e1' ->
      ECC_RedClosR g e2 e2' ->
      ECC_RedClosR g A A'   ->
      ECC_RedClosR g (ePair e1 e2 A) (ePair e1' e2' A')
  | R_CongApp (g: ECCenv) (e1 e1' e2 e2': ECCexp) :
      ECC_RedClosR g e1 e1' ->
      ECC_RedClosR g e2 e2' ->
      ECC_RedClosR g (eApp e1 e2) (eApp e1' e2')
  | R_CongFst (g: ECCenv) (V V': ECCexp) :
      ECC_RedClosR g V V' ->
      ECC_RedClosR g (eFst V) (eFst V')
  | R_CongSnd (g: ECCenv) (V V': ECCexp) :
      ECC_RedClosR g V V' ->
      ECC_RedClosR g (eSnd V) (eSnd V')
  | R_CongIf (g: ECCenv) (e e' e1 e1' e2 e2': ECCexp) :
      ECC_RedClosR g e e' ->
      ECC_RedClosR g e1 e1' ->
      ECC_RedClosR g e2 e2' ->
      ECC_RedClosR g (eIf e e1 e2) (eIf e' e1' e2')
.

Hint Constructors ECC_RedClosR.



Inductive ECC_Equiv: ECCenv -> ECCexp -> ECCexp -> Prop :=
  | E_Equiv (g: ECCenv) (e e1 e2: ECCexp) :
      ECC_RedClosR g e1 e ->
      ECC_RedClosR g e2 e ->
      ECC_Equiv g e1 e2
  | E_EquivIta1 (g: ECCenv) (e1 A e e2 e2': ECCexp) (x: atom) :
      ECC_RedClosR g e1 (eAbs x A e) ->
      ECC_RedClosR g e2 e2' ->
      ECC_Equiv (gAssum g x A) e (eApp e2' (eId x)) ->
      ECC_Equiv g e1 e2
  | E_EquivIta2 (g: ECCenv) (e e1 e1' e2 A : ECCexp) (x: atom) :
      ECC_RedClosR g e1 e1' ->
      ECC_RedClosR g e2 (eAbs x A e) ->
      ECC_Equiv (gAssum g x A) (eApp e1' (eId x)) e ->
      ECC_Equiv g e1 e2
  | E_EquivAlpha (g: ECCenv) (e1 e2: ECCexp):
      ECC_Aeq e1 e2 ->
      ECC_Equiv g e1 e2
.

Hint Constructors ECC_Equiv.

(* Typing *)

Inductive ECC_sub_type: ECCenv -> ECCexp -> ECCexp -> Prop :=
| ST_Cong (g: ECCenv) (A B: ECCexp) :
  ECC_Equiv g A B ->
  ECC_sub_type g A B
| ST_Cum (g: ECCenv) (i: nat) :
  ECC_sub_type g (eUni (uType i)) (eUni (uType (S i)))
| ST_Pi (g: ECCenv) (A1 A2 B1 B2: ECCexp) (x1 x2: atom) :
  (ECC_Equiv g A1 A2) ->
  (ECC_sub_type (gAssum g x1 A2) B1 (subst x2 (eId x1) B2)) -> (* eId x1 ?*)
  (ECC_sub_type g (ePi x1 A1 B1) (ePi x2 A2 B2))
.

Hint Constructors ECC_sub_type.

Inductive ECC_has_type: ECCenv -> ECCexp -> ECCexp -> Prop :=
| T_Ax_Prop (g: ECCenv) :
  (ECC_has_type g (eUni uProp) (eUni (uType 0)))
| T_Ax_Type (g: ECCenv) (i: nat) :
  (ECC_has_type g (eUni (uType i)) (eUni (uType (S i))))
| T_Var (g: ECCenv) (x: atom) (A: ECCexp) :
  (ECC_LookupTypeR g x A) -> (* this needs adjustment *)
  (ECC_has_type g (eId x) A)
| T_Let (g: ECCenv) (e e' A B: ECCexp) (x: atom):
  (ECC_has_type g e A) ->
  (ECC_has_type (gDef (gAssum g x A) x e) e' B) ->
  (ECC_has_type g (eLet x e e') (subst x e B))
| T_Prod_Prop (g: ECCenv) (x: atom) (A B: ECCexp) (i: nat):
  (ECC_has_type g A (eUni (uType i))) ->
  (ECC_has_type (gAssum g x A) B (eUni (uProp))) ->
  (ECC_has_type g (ePi x A B) (eUni (uProp)))
| T_Prod_Type (g: ECCenv) (x: atom) (A B: ECCexp) (i: nat):
  (ECC_has_type g A (eUni (uType i))) ->
  (ECC_has_type (gAssum g x A) B (eUni (uType i))) ->
  (ECC_has_type g (ePi x A B) (eUni (uType i)))
| T_Lam (g: ECCenv) (x: atom) (A e B: ECCexp) :
  (ECC_has_type (gDef g x A) e B) ->
  (ECC_has_type g (eAbs x A e) (ePi x A B))
| T_App (g: ECCenv) (x: atom) (e e' A' B: ECCexp) :
  (ECC_has_type g e (ePi x A' B)) ->
  (ECC_has_type g e' A') ->
  (ECC_has_type g (eApp e e') (subst x e B))
| T_Sig (g: ECCenv) (x: atom) (A B: ECCexp) (i: nat) :
  (ECC_has_type g A (eUni (uType i))) ->
  (ECC_has_type (gAssum g x A) B (eUni (uType i))) -> (* should these be the same i*)
  (ECC_has_type g (eSig x A B) (eUni (uType i)))
| T_Pair (g: ECCenv) (e1 e2 A B: ECCexp) (x: atom) :
  (ECC_has_type g e1 A) ->
  (ECC_has_type g e2 (subst x e1 B)) ->
  (ECC_has_type g (ePair e1 e2 (eSig x A B)) (eSig x A B))
| T_Fst (g: ECCenv) (e A B: ECCexp) (x: atom) :
  (ECC_has_type g e (eSig x A B)) ->
  (ECC_has_type g (eFst e) A)
| T_Snd (g: ECCenv) (e A B: ECCexp) (x: atom) :
  (ECC_has_type g e (eSig x A B)) ->
  (ECC_has_type g (eSnd e) (subst x (eFst e) B))
| T_Bool (g: ECCenv):
  (ECC_has_type g (eBool) (eUni (uType 0)))
| T_True (g: ECCenv):
  (ECC_has_type g (eTru) (eBool))
| T_False (g: ECCenv):
  (ECC_has_type g (eFls) (eBool))
| T_If (g: ECCenv) (B U e e1 e2: ECCexp) (x: atom):
  (ECC_has_type (gAssum g x (eBool)) B U) ->
  (ECC_has_type g e (eBool)) ->
  (ECC_has_type g e1 (subst x (eTru) B)) ->
  (ECC_has_type g e2 (subst x (eFls) B)) ->
  (ECC_has_type g (eIf e e1 e2) (subst x e B))
| T_Conv (g: ECCenv) (e A B U: ECCexp) :
  (ECC_has_type g e A) ->
  (ECC_has_type g B U) ->
  (ECC_sub_type g A B) ->
  (ECC_has_type g e B)
.

Fixpoint ECC_type (g: ECCenv) (e: ECCexp): option Prop :=


Hint Constructors ECC_has_type.

Goal ECC_has_type gEmpty (eUni uProp) (eUni (uType 0)).
Proof.
intuition.
Qed.

(* ECC Notation *)

Bind Scope ECC_scope with ECCexp.
Bind Scope ECC_scope with ECCuni.
Bind Scope ECC_scope with ECCenv.
Delimit Scope ECC_scope with ECC.
Coercion eId: atom >-> ECCexp.

Notation "'type' x" := (eUni (uType x)) (at level 50):  ECC_scope.
Notation "'prop'" := (eUni uProp) (at level 50):  ECC_scope.
Definition example_Type := (type 3)%ECC: ECCexp.
Definition example_Prop := (prop)%ECC: ECCexp.

Notation "{ e1 e2 }" := (eApp e1 e2) (at level 50,e1 at level 9):  ECC_scope.
Definition example_App := { X Y }%ECC: ECCexp.

Notation "'LET' x ':=' A 'in' B" := (eLet x A B) (at level 50, format "'[v' 'LET'  x  ':='  A '/' 'in' '['  B ']' ']'") : ECC_scope.
Definition example_Let := (LET X := Y in Z)%ECC : ECCexp.
Print example_Let.
Definition F:= fresh (X::Y::Z::nil).
Definition example_Let2 := (LET X := (type 3) in LET F := (LET X := (type 2) in X) in ({X F}))%ECC.
Print example_Let2.

Notation "'Pi' x : A '->' B" := (ePi x A B) (at level 50, x at level 9, A at level 9) : ECC_scope.
Definition example_Pi := (Pi X : F -> Y)%ECC : ECCexp.
Notation "'\'  x : A  '->'  B" := (eAbs x A B) (at level 50, x at level 9, A at level 9) : ECC_scope.
Definition example_Abs := (\ X: Y -> Z)%ECC : ECCexp.
Notation "'Sig' x : A '..' B" := (eSig x A B) (at level 50, x at level 1, A at level 1): ECC_scope.
Definition example_Sig := (Sig X : Y .. Z)%ECC : ECCexp.
Notation "< e1 , e2 > 'as' A" := (ePair e1 e2 A) (at level 50, e1 at level 5, e2 at level 5, A at level 5): ECC_scope.
Definition example_Pair := (< X, Y > as (Sig X : Y .. Z))%ECC : ECCexp.
Notation "'fst' e" := (eFst e) (at level 50, e at level 5): ECC_scope.
Notation "'snd' e" := (eSnd e) (at level 50, e at level 5): ECC_scope.

Definition example_ycombinator := (\F:(type 3) -> ({(\X:(type 2) -> ({F {X X}})) (\X:(type 2) -> ({F {X X}}))}))%ECC.
Print example_ycombinator.

Compute subst X Y (LET Y := type 1 in X).

Goal ECC_RedClosR gEmpty (LET X := Y in LET Y := type 1 in X) Y.
Proof.
cut (ECC_RedR gEmpty (LET X := Y in LET Y := type 1 in X)%ECC (subst X (eId Y) (LET Y := type 1 in X))%ECC).
- cut (ECC_RedR gEmpty (subst X (eId Y) (LET Y := type 1 in X))%ECC Y). 
  + eauto.
  + cbv. apply R_Let.
- cbv. apply R_Let.
Qed.

Goal ECC_has_type gEmpty (fst (<eTru , eFls> as (Sig X : eBool .. eBool))) eBool.
eauto.
Qed.

Goal ECC_has_type gEmpty (fst (<eTru , eFls> as 
                            (Sig X : eBool .. (eIf X eBool (Pi Y : eBool -> eBool))))) eBool.
eapply T_Fst. eapply T_Pair.
  - apply T_True.
  - cbv. apply T_Conv with (A := eBool) (U := (type 0)%ECC).
    + apply T_False.
    + eapply T_Conv.
      * apply T_If with (U:=(type 1)%ECC). 
        -- auto.
        -- auto.
        -- auto.
        -- cbn. eapply T_Prod_Type.
          ++ auto.
          ++ auto.
      * auto.
      * cbn. apply ST_Cong. apply E_EquivAlpha. apply aeq_id.
    + apply ST_Cong. apply E_Equiv with (e:= eBool).
      * auto.
      * eauto.
Unshelve. exact 1.
Qed.
   

(* End ECC.*)

(* (* Module ECCA. *)
 *)
(* -=ECCA Definition=- *)

Inductive ECCAval: Type :=
  | avId (x: atom)
  | avUni (U: ECCuni)
  | avPi (x: atom) (A B: ECCAconf)
  | avAbs (x: atom) (A B: ECCAconf)
  | avSig (x: atom) (A B: ECCAconf)
  | avPair (v1 v2: ECCAval) (A: ECCAconf)
  | avTru
  | avFls
  | avBool
with
ECCAconf: Type :=
  | acfComp (e: ECCAcomp)
  | acfLet (x: atom) (A: ECCAcomp) (B: ECCAconf)
  | acfIf (v: ECCAval) (m1 m2: ECCAconf)
with
ECCAcomp: Type :=
  | acpApp (v1 v2: ECCAval)
  | acpVal (v: ECCAval)
  | acpFst (v: ECCAval)
  | acpSnd (v: ECCAval)
  | acpSubst (x arg body: ECCAval)
.

Inductive ECCAcont: Type :=
  | actHole
  | actLetHole (x: atom) (B: ECCAconf)
.

Inductive ECCAenv: Type :=
  | agEmpty
  | agAssume (x A: ECCAval)
  | agDef (x V: ECCAval)
(*| agValEqVal???*)
.


(* -=ECCA Notation=- *)

Bind Scope ECCA_scope with ECCAval.
Bind Scope ECCA_scope with ECCAconf.
Bind Scope ECCA_scope with ECCAcomp.
Bind Scope ECCA_scope with ECCAcont.
Delimit Scope ECCA_scope with ECCA.
Coercion avId: atom >-> ECCAval.
Definition natToAtom (i: nat) : atom :=
i.
Coercion natToAtom: nat >-> atom.
Coercion acpVal: ECCAval >-> ECCAcomp.
Coercion acfComp: ECCAcomp >-> ECCAconf.

Notation "'type' x" := (avUni (uType x)) (at level 50):  ECCA_scope.
Notation "'prop'" := (avUni uProp) (at level 50):  ECCA_scope.
Definition example_aType := (type 3)%ECCA: ECCAval.
Definition example_aProp := (prop)%ECCA: ECCAval.

Notation "{ e1 e2 }" := (acpApp e1 e2) (at level 50,e1 at level 9):  ECCA_scope.
Definition example_aApp := { X Y }%ECCA: ECCAcomp.

Notation "'LET' x ':=' A 'in' B" := (acfLet x A B) (at level 50, format "'[v' 'LET'  x  ':='  A '/' 'in' '['  B ']' ']'") : ECCA_scope.
Definition example_aLet := (LET X := Y in Z)%ECCA : ECCAconf.
Print example_aLet.
Definition example_aLet2 := (LET X := (type 3) in LET F := (LET X := (type 2) in X) in ({X F}))%ECC.
Print example_aLet2.

Notation "'P' x : A '->' B" := (avPi x A B) (at level 50, x at level 9, A at level 9) : ECCA_scope.
Definition example_aPi := (P X : Y -> Z)%ECCA : ECCAval.
Notation "'\' x : A '->' B" := (avAbs x A B) (at level 50, x at level 9, A at level 9) : ECCA_scope.
Definition example_aAbs := (\ X : Y -> Z)%ECCA : ECCAval.

Notation "'[]'" := (actHole) (at level 50) : ECCA_scope.
Definition aHole := []%ECCA.
Notation "'LET' x ':=' '[]' 'in' B" := (actLetHole x B) (at level 50) : ECCA_scope.
Definition example_aLetHole := (LET X := [] in X)%ECCA.
Print example_aLetHole.

(* End ECCA. *)
(* 
Inductive ECCA_Aeq : ECCexp -> ECCexp -> Prop :=
  | aeq_id (e: ECCexp):
    ECC_Aeq e e
  | aeq_var (x: atom):
     ECC_Aeq (eId x) (eId x)
  | aeq_abs_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (eAbs x t1 b1) (eAbs x t2 b2)
  | aeq_abs_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (eAbs x t1 b1) (eAbs y t2 b2)
  | aeq_pi_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (ePi x t1 b1) (ePi x t2 b2)
  | aeq_pi_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (ePi x t1 b1) (ePi y t2 b2)
  | aeq_let_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (eLet x t1 b1) (eLet x t2 b2)
  | aeq_let_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (eLet x t1 b1) (eLet y t2 b2)
  | aeq_sig_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (eSig x t1 b1) (eSig x t2 b2)
  | aeq_sig_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (eSig x t1 b1) (eSig y t2 b2)
  | aeq_app (t1 t2 t1' t2': ECCexp):
     ECC_Aeq t1 t1' -> ECC_Aeq t2 t2' ->
     ECC_Aeq (eApp t1 t2) (eApp t1' t2')
  | aeq_pair (t1 t2 t1' t2' A A': ECCexp):
     ECC_Aeq t1 t1' -> ECC_Aeq t2 t2' ->
     ECC_Aeq A A' ->
     ECC_Aeq (ePair t1 t2 A) (ePair t1' t2' A')
  | aeq_eFst (e e': ECCexp):
     ECC_Aeq e e' ->
     ECC_Aeq (eFst e) (eFst e')
  | aeq_eSnd (e e': ECCexp):
     ECC_Aeq e e' ->
     ECC_Aeq (eSnd e) (eSnd e')
  | aeq_if (e1 e2 e3 e1' e2' e3': ECCexp):
     ECC_Aeq e1 e1' ->
     ECC_Aeq e2 e2' ->
     ECC_Aeq e3 e3' ->
     ECC_Aeq (eIf e1 e2 e3) (eIf e1' e2' e3').

 *)
(* ===ECC to ECCA translation== *)


Fixpoint fill_hole (e: ECCAcomp) (K: ECCAcont): ECCAconf :=
  match K with
    | actHole => acfComp e
    | actLetHole x B => acfLet x e B
end.

(* Plan: starter function starts namestate at max of atoms in the ECCexp, so all new atoms are higher than old atoms. *)

(* {ns : NameState} *)

Fixpoint trans  (ns: atom) (e: ECCexp) (K: ECCAcont) : ECCAconf :=
  let X := (S ns) in
  let Y := (S (S ns)) in
  let Z := (S (S (S ns))) in
  match e with
    | eId x => (fill_hole (acpVal (avId x)) K)
    | ePi x A B => (fill_hole (acpVal (avPi (x) (trans ns A actHole) (trans ns B actHole))) K)
    | eAbs x A e => (fill_hole (acpVal (avAbs x (trans ns A actHole) (trans ns e actHole))) K)
    | eApp e1 e2 =>
        (trans X e1 (actLetHole X
            (trans Y e2 (actLetHole Y
                (fill_hole (acpApp (avId X) (avId Y)) K)))))
    | eLet x e1 e2 => (trans ns e1 (actLetHole x
                          (trans (ns) e2 K)))
    | eSig x A B => (fill_hole (acpVal (avSig x (trans ns A actHole) (trans ns B actHole))) K)
    | ePair e1 e2 A => (trans X e1 (actLetHole X
            (trans Y e2 (actLetHole Y
               (trans Z A (actLetHole Z
                (fill_hole (avPair (avId X) (avId Y) (avId Z)) K)))))))
    | eFst e => (trans X e (actLetHole X
                   (fill_hole (acpFst (avId X)) K)))
    | eSnd e => (trans X e (actLetHole X
                   (fill_hole (acpSnd X) K)))
    | eTru => (fill_hole (acpVal avTru) K)
    | eFls => (fill_hole (acpVal avFls) K)
    | eBool=> (fill_hole (acpVal avBool) K)
    | eUni u => (fill_hole (acpVal (avUni u)) K)
    | eIf e e1 e2 => (trans X e (actLetHole X 
                        (acfIf (avId X) 
                            (trans Y e1 (actLetHole Y (fill_hole (acpSubst X avTru (avId Y)) K)))
                            (trans Y e1 (actLetHole Y (fill_hole (acpSubst X avFls (avId Y)) K))))))
end.

Definition transStarter (e: ECCexp):=
  trans (fresh (FV e)) e actHole
.

Compute transStarter (LET X := Y in LET Y := type 1 in X)%ECC.
Compute transStarter (fst (<eTru , eFls> as 
                            (Sig X : eBool .. (eIf X eBool (Pi Y : eBool -> eBool))))).
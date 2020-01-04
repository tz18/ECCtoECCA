Require Import Atom.

(* -=ECC Definition=- *)

Inductive ECCexp: Type :=
  | Id (x: atom)
  | Uni (U: ECCuni)
  | Pi (x: atom) (A B: ECCexp)
  | Abs (x: atom) (A e: ECCexp)
  | App  (e1 e2: ECCexp)
  | Let (x: atom) (e1 e2: ECCexp)
  | Sig (x: atom) (A B: ECCexp)
  | Pair (e1 e2 A: ECCexp)
  | Fst (e: ECCexp)
  | Snd (e: ECCexp)
  | If (e e1 e2: ECCexp)
  | Tru
  | Fls
  | Bool
.

Inductive ECCenv: Type :=
  | Empty
  | Assum (g: ECCenv) (x: atom) (A: ECCexp)
  | Def (g: ECCenv) (x: atom) (e: ECCexp)
.

Fixpoint ECCsize (e: ECCexp) : nat :=
  match e with
  | Id _ => 1
  | Uni _ => 1
  | Pi _ A B => 1 + (ECCsize A) + (ECCsize B)
  | Abs _ A e => 1 + (ECCsize A) + (ECCsize e)
  | App e1 e2 => 1 + (ECCsize e1) + (ECCsize e2)
  | Let _ e1 e2 => 1 + (ECCsize e1) + (ECCsize e2)
  | Sig _ A B => 1 + (ECCsize A) + (ECCsize B)
  | Pair e1 e2 A => 1 + (ECCsize e1) + (ECCsize e2) + (ECCsize A)
  | Fst e => 1 + (ECCsize e)
  | Snd e => 1 + (ECCsize e)
  | If e e1 e2 => 1 + (ECCsize e) + (ECCsize e1) + (ECCsize e2)
  | Tru => 1
  | Fls => 1
  | Bool => 1
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
    ECC_LookupTypeR (Assum g' x A) x A
  | LT_AssumRest (g: ECCenv) (x x': atom) (A a': ECCexp):
    ECC_LookupTypeR g x A ->
    (x <> x') ->
    (ECC_LookupTypeR (Assum g x' a') x A)
  | LT_DefRest (g: ECCenv) (x x': atom) (A a': ECCexp):
    ECC_LookupTypeR g x A ->
(*     (x <> x') -> *)
    (ECC_LookupTypeR (Def g x' a') x A)
.

Inductive ECC_LookupDefR : ECCenv -> atom -> ECCexp -> Prop:=
  | LD_gFirst (g': ECCenv) (x: atom) (e A: ECCexp):
    ECC_LookupDefR (Assum (Def g' x e) x A) x e
  | LD_AssumRest (g: ECCenv) (x x': atom) (e a': ECCexp):
    ECC_LookupDefR g x e ->
    (x <> x') ->
    (ECC_LookupDefR (Assum g x' a') x e)
  | LD_DefRest (g: ECCenv) (x x': atom) (e e': ECCexp):
    ECC_LookupDefR g x e ->
    (x <> x') ->
    (ECC_LookupDefR (Def g x' e') x e)
.
(* Q: what if looking up a type and get a value first, or vice versa? *)

Hint Constructors ECC_LookupTypeR.

Example ECC_LookupFirstExample:
ECC_LookupTypeR (Assum Empty X Tru) X Tru.
Proof.
  auto.
Qed.

Example ECC_LookupRestExample:
X <> Y -> ECC_LookupTypeR (Assum (Assum Empty X Tru) Y Fls) X Tru.
Proof.
  auto.  (* WOW!*)
Qed.

Fixpoint ECC_LookupType (g: ECCenv) (x: atom): option ECCexp :=
match g with
  | Empty => None
  | Assum g' x' A => if (x' =? x) then Some A else (ECC_LookupType g' x)
  | Def g' x' e => (ECC_LookupType g' x)
end.

Fixpoint ECC_LookupDef (g: ECCenv) (x: atom): option ECCexp :=
match g with
  | Empty => None
  | Assum g' x' A => if (x' =? x) then match g' with
      | Empty => None
      | Assum g'' x'' A => None
      | Def g' x'' e => if (x'' =? x) then Some e else None
      end      
      else (ECC_LookupDef g' x)
  | Def g' x' e => if (x' =? x) then None else (ECC_LookupDef g' x)
end.

Lemma ECC_EmptyImpliesNothing : forall (x: atom) (A: ECCexp), ECC_LookupTypeR Empty x A -> False.
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
  | Id x => singleton x
  | Uni U => empty
  | Pi x A B =>  union (FV A) (remove x (FV B))
  | Abs x A e => union (FV A) (remove  x (FV e))
  | App  e1 e2 => (union (FV e1) (FV e2))
  | Let x e1 e2 => (union (FV e1) (FV e2))
  | Sig x A B => (union (FV A) (remove  x (FV B)))
  | Pair e1 e2 A => (union (union  (FV e1) (FV e2)) (FV A))
  | Fst e => (FV e)
  | Snd e => (FV e)
  | If e e1 e2 => (union (union  (FV e) (FV e1)) (FV e2))
  | Tru => empty
  | Fls => empty
  | Bool => empty
end.

(*Let's get nominal!*)

Fixpoint swap (x:atom) (y:atom) (t:ECCexp) : ECCexp :=
  match t with
  | Id z     => Id (swap_var x y z)
  | Abs z A t1  => Abs (swap_var x y z) (swap x y A) (swap x y t1)
  | App t1 t2 => App (swap x y t1) (swap x y t2)
  | Pi x' A B => Pi (swap_var x y x') (swap x y A) (swap x y B)
  | Let x' e1 e2 => Let (swap_var x y x') (swap x y e1) (swap x y e2)
  | Sig x' A B => Sig (swap_var x y x') (swap x y A) (swap x y B)
  | Pair e1 e2 A => Pair (swap x y e1) (swap x y e2) (swap x y A)
  | Fst e => (Fst (swap x y e))
  | Snd e => (Snd (swap x y e))
  | If e e1 e2 => (If (swap x y e) (swap x y e1) (swap x y e2))
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
  | Id x' => if (x =? x') then arg else body
  | Abs x' A e =>
      if (x =? x')
        then (Abs x' (substWork x arg A FVInArg) e)
        else let xnew := fresh (union FVInArg (FV e)) in
                    (Abs xnew (substWork x arg A FVInArg) (substWork x arg (swap x' xnew e) FVInArg))
  | Pi x' A B =>
      if (x =? x')
        then (Pi x' (substWork x arg A FVInArg) B)
        else let xnew := fresh (union FVInArg (FV B)) in
                (Pi xnew (substWork x arg A FVInArg) (substWork x arg (swap x' xnew B) FVInArg))
  | Let x' A B =>
      if (x =? x')
        then (Let x' (substWork x arg A FVInArg) B)
        else let xnew := fresh (union FVInArg (FV B)) in
                (Let xnew (substWork x arg A FVInArg) (substWork x arg (swap x' xnew B) FVInArg))
  | Sig x' A B =>
      if (x =? x')
        then (Sig x' (substWork x arg A FVInArg) B)
        else let xnew := fresh (union FVInArg (FV B)) in
                (Sig xnew (substWork x arg A FVInArg) (substWork x arg (swap x' xnew B) FVInArg))
  | App e1 e2 => (App (substWork x arg e1 FVInArg) (substWork x arg e2 FVInArg))
  | Uni U => body
  | Pair e1 e2 A => (Pair (substWork x arg e1 FVInArg) (substWork x arg e2 FVInArg) (substWork x arg A FVInArg))
  | Fst e => (Fst (substWork x arg e FVInArg))
  | Snd e => (Snd (substWork x arg e FVInArg))
  | If e e1 e2 => (If (substWork x arg e FVInArg) (substWork x arg e1 FVInArg) (substWork x arg e2 FVInArg))
  | Tru => Tru
  | Fls => Fls
  | Bool => Bool
end.
Obligations.
Solve Obligations with (Tactics.program_simpl; cbn; omega).
Solve Obligations with (Tactics.program_simpl; cbn; rewrite -> swap_size_eq; omega).

Definition subst (x: atom) (arg body: ECCexp):= substWork x arg body (FV arg).

Inductive ECC_Aeq : ECCexp -> ECCexp -> Prop :=
  | aeq_id (e: ECCexp):
    ECC_Aeq e e
  | aeq_var (x: atom):
     ECC_Aeq (Id x) (Id x)
  | aeq_abs_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (Abs x t1 b1) (Abs x t2 b2)
  | aeq_abs_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (Abs x t1 b1) (Abs y t2 b2)
  | aeq_pi_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (Pi x t1 b1) (Pi x t2 b2)
  | aeq_pi_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (Pi x t1 b1) (Pi y t2 b2)
  | aeq_let_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (Let x t1 b1) (Let x t2 b2)
  | aeq_let_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (Let x t1 b1) (Let y t2 b2)
  | aeq_sig_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (Sig x t1 b1) (Sig x t2 b2)
  | aeq_sig_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     (mem x (FV b2)) = false ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (Sig x t1 b1) (Sig y t2 b2)
  | aeq_app (t1 t2 t1' t2': ECCexp):
     ECC_Aeq t1 t1' -> ECC_Aeq t2 t2' ->
     ECC_Aeq (App t1 t2) (App t1' t2')
  | aeq_pair (t1 t2 t1' t2' A A': ECCexp):
     ECC_Aeq t1 t1' -> ECC_Aeq t2 t2' ->
     ECC_Aeq A A' ->
     ECC_Aeq (Pair t1 t2 A) (Pair t1' t2' A')
  | aeq_Fst (e e': ECCexp):
     ECC_Aeq e e' ->
     ECC_Aeq (Fst e) (Fst e')
  | aeq_Snd (e e': ECCexp):
     ECC_Aeq e e' ->
     ECC_Aeq (Snd e) (Snd e')
  | aeq_if (e1 e2 e3 e1' e2' e3': ECCexp):
     ECC_Aeq e1 e1' ->
     ECC_Aeq e2 e2' ->
     ECC_Aeq e3 e3' ->
     ECC_Aeq (If e1 e2 e3) (If e1' e2' e3').

Hint Constructors ECC_Aeq.

Timeout 30 Compute substWork X (Tru) (Id X) (FV Tru). 
Compute substWork X (Tru) (Abs Y (Bool) (Id X)) (FV Tru).
Compute substWork X (Tru) (Abs X (Id X) (Id X)) (FV Tru).
Eval vm_compute in substWork X (Tru) (Abs X (Id X) (Id X)) (FV Tru).


(* -Step- *)
Inductive ECC_RedR : ECCenv -> ECCexp -> ECCexp -> Prop :=
  | R_ID (g: ECCenv) (x: atom) (e': ECCexp) :
    ECC_LookupDefR g x e' -> ECC_RedR g (Id x) e'
  | R_App (g: ECCenv) (x: atom) (A body arg: ECCexp) :
    ECC_RedR g (App (Abs x A body) arg) (subst x arg body) (*do anything with env here?*)
  | R_Fst (g: ECCenv) (e1 e2 A: ECCexp) :
    ECC_RedR g (Fst (Pair e1 e2 A)) e1
  | R_Snd (g: ECCenv) (e1 e2 A: ECCexp) :
    ECC_RedR g (Snd (Pair e1 e2 A)) e2
  | R_Let (g: ECCenv) (x: atom) (e1 e2: ECCexp) :
    ECC_RedR g (Let x e1 e2) (subst x e1 e2)  (*or here?*)
  | R_IfTru (g: ECCenv) (e1 e2: ECCexp) :
    ECC_RedR g (If Tru e1 e2) e1
  | R_IfFls (g: ECCenv) (e1 e2: ECCexp) :
    ECC_RedR g (If Fls e1 e2) e2
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
      ECC_RedClosR (Def g x e) e1 e2 ->
      ECC_RedClosR g (Let x e e1) (Let x e e2)
  | R_CongLam1 (g: ECCenv) (A A' e e': ECCexp) (x: atom) :
      ECC_RedClosR g A A' ->
      ECC_RedClosR (Assum g x A) e e' ->
      ECC_RedClosR g (Abs x A e) (Abs x A' e')
  | R_CongPi (g: ECCenv) (A A' B B': ECCexp) (x: atom) :
      ECC_RedClosR g A A' ->
      ECC_RedClosR (Assum g x A) B B' ->
      ECC_RedClosR g (Pi x A B) (Pi x A' B')
  | R_CongSig (g: ECCenv) (A A' B B': ECCexp) (x: atom) :
      ECC_RedClosR g A A' ->
      ECC_RedClosR (Assum g x A) B B' ->
      ECC_RedClosR g (Sig x A B) (Sig x A' B')
  | R_CongPair (g: ECCenv) (e1 e1' e2 e2' A A': ECCexp) :
      ECC_RedClosR g e1 e1' ->
      ECC_RedClosR g e2 e2' ->
      ECC_RedClosR g A A'   ->
      ECC_RedClosR g (Pair e1 e2 A) (Pair e1' e2' A')
  | R_CongApp (g: ECCenv) (e1 e1' e2 e2': ECCexp) :
      ECC_RedClosR g e1 e1' ->
      ECC_RedClosR g e2 e2' ->
      ECC_RedClosR g (App e1 e2) (App e1' e2')
  | R_CongFst (g: ECCenv) (V V': ECCexp) :
      ECC_RedClosR g V V' ->
      ECC_RedClosR g (Fst V) (Fst V')
  | R_CongSnd (g: ECCenv) (V V': ECCexp) :
      ECC_RedClosR g V V' ->
      ECC_RedClosR g (Snd V) (Snd V')
  | R_CongIf (g: ECCenv) (e e' e1 e1' e2 e2': ECCexp) :
      ECC_RedClosR g e e' ->
      ECC_RedClosR g e1 e1' ->
      ECC_RedClosR g e2 e2' ->
      ECC_RedClosR g (If e e1 e2) (If e' e1' e2')
.

Hint Constructors ECC_RedClosR.



Inductive ECC_Equiv: ECCenv -> ECCexp -> ECCexp -> Prop :=
  | E_Equiv (g: ECCenv) (e e1 e2: ECCexp) :
      ECC_RedClosR g e1 e ->
      ECC_RedClosR g e2 e ->
      ECC_Equiv g e1 e2
  | E_EquivIta1 (g: ECCenv) (e1 A e e2 e2': ECCexp) (x: atom) :
      ECC_RedClosR g e1 (Abs x A e) ->
      ECC_RedClosR g e2 e2' ->
      ECC_Equiv (Assum g x A) e (App e2' (Id x)) ->
      ECC_Equiv g e1 e2
  | E_EquivIta2 (g: ECCenv) (e e1 e1' e2 A : ECCexp) (x: atom) :
      ECC_RedClosR g e1 e1' ->
      ECC_RedClosR g e2 (Abs x A e) ->
      ECC_Equiv (Assum g x A) (App e1' (Id x)) e ->
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
  ECC_sub_type g (Uni (uType i)) (Uni (uType (S i)))
| ST_Pi (g: ECCenv) (A1 A2 B1 B2: ECCexp) (x1 x2: atom) :
  (ECC_Equiv g A1 A2) ->
  (ECC_sub_type (Assum g x1 A2) B1 (subst x2 (Id x1) B2)) -> (* Id x1 ?*)
  (ECC_sub_type g (Pi x1 A1 B1) (Pi x2 A2 B2))
.

Hint Constructors ECC_sub_type.

Inductive ECC_has_type: ECCenv -> ECCexp -> ECCexp -> Prop :=
| T_Ax_Prop (g: ECCenv) :
  (ECC_has_type g (Uni uProp) (Uni (uType 0)))
| T_Ax_Type (g: ECCenv) (i: nat) :
  (ECC_has_type g (Uni (uType i)) (Uni (uType (S i))))
| T_Var (g: ECCenv) (x: atom) (A: ECCexp) :
  (ECC_LookupTypeR g x A) -> (* this needs adjustment *)
  (ECC_has_type g (Id x) A)
| T_Let (g: ECCenv) (e e' A B: ECCexp) (x: atom):
  (ECC_has_type g e A) ->
  (ECC_has_type (Def (Assum g x A) x e) e' B) ->
  (ECC_has_type g (Let x e e') (subst x e B))
| T_Prod_Prop (g: ECCenv) (x: atom) (A B: ECCexp) (i: nat):
  (ECC_has_type g A (Uni (uType i))) ->
  (ECC_has_type (Assum g x A) B (Uni (uProp))) ->
  (ECC_has_type g (Pi x A B) (Uni (uProp)))
| T_Prod_Type (g: ECCenv) (x: atom) (A B: ECCexp) (i: nat):
  (ECC_has_type g A (Uni (uType i))) ->
  (ECC_has_type (Assum g x A) B (Uni (uType i))) ->
  (ECC_has_type g (Pi x A B) (Uni (uType i)))
| T_Lam (g: ECCenv) (x: atom) (A e B: ECCexp) :
  (ECC_has_type (Assum g x A) e B) ->
  (ECC_has_type g (Abs x A e) (Pi x A B))
| T_App (g: ECCenv) (x: atom) (e e' A' B: ECCexp) :
  (ECC_has_type g e (Pi x A' B)) ->
  (ECC_has_type g e' A') ->
  (ECC_has_type g (App e e') (subst x e B))
| T_Sig (g: ECCenv) (x: atom) (A B: ECCexp) (i: nat) :
  (ECC_has_type g A (Uni (uType i))) ->
  (ECC_has_type (Assum g x A) B (Uni (uType i))) -> (* should these be the same i*)
  (ECC_has_type g (Sig x A B) (Uni (uType i)))
| T_Pair (g: ECCenv) (e1 e2 A B: ECCexp) (x: atom) :
  (ECC_has_type g e1 A) ->
  (ECC_has_type g e2 (subst x e1 B)) ->
  (ECC_has_type g (Pair e1 e2 (Sig x A B)) (Sig x A B))
| T_Fst (g: ECCenv) (e A B: ECCexp) (x: atom) :
  (ECC_has_type g e (Sig x A B)) ->
  (ECC_has_type g (Fst e) A)
| T_Snd (g: ECCenv) (e A B: ECCexp) (x: atom) :
  (ECC_has_type g e (Sig x A B)) ->
  (ECC_has_type g (Snd e) (subst x (Fst e) B))
| T_Bool (g: ECCenv):
  (ECC_has_type g (Bool) (Uni (uType 0)))
| T_True (g: ECCenv):
  (ECC_has_type g (Tru) (Bool))
| T_False (g: ECCenv):
  (ECC_has_type g (Fls) (Bool))
| T_If (g: ECCenv) (B U e e1 e2: ECCexp) (x: atom):
  (ECC_has_type (Assum g x (Bool)) B U) ->
  (ECC_has_type g e (Bool)) ->
  (ECC_has_type g e1 (subst x (Tru) B)) ->
  (ECC_has_type g e2 (subst x (Fls) B)) ->
  (ECC_has_type g (If e e1 e2) (subst x e B))
| T_Conv (g: ECCenv) (e A B U: ECCexp) :
  (ECC_has_type g e A) ->
  (ECC_has_type g B U) ->
  (ECC_sub_type g A B) ->
  (ECC_has_type g e B)
.


Hint Constructors ECC_has_type.

Goal ECC_has_type Empty (Uni uProp) (Uni (uType 0)).
Proof.
intuition.
Qed.

(* ECC Notation *)

Bind Scope ECC_scope with ECCexp.
Bind Scope ECC_scope with ECCuni.
Bind Scope ECC_scope with ECCenv.
Delimit Scope ECC_scope with ECC.
Coercion Id: atom >-> ECCexp.

Notation "'type' x" := (Uni (uType x)) (at level 50):  ECC_scope.
Notation "'prop'" := (Uni uProp) (at level 50):  ECC_scope.
Definition example_Type := (type 3)%ECC: ECCexp.
Definition example_Prop := (prop)%ECC: ECCexp.

Notation "{ e1 e2 }" := (App e1 e2) (at level 50,e1 at level 9):  ECC_scope.
Definition example_App := { X Y }%ECC: ECCexp.

Notation "'LET' x ':=' A 'in' B" := (Let x A B) (at level 50, format "'[v' 'LET'  x  ':='  A '/' 'in' '['  B ']' ']'") : ECC_scope.
Definition example_Let := (LET X := Y in Z)%ECC : ECCexp.
Print example_Let.
Definition F:= fresh (X::Y::Z::nil).
Definition example_Let2 := (LET X := (type 3) in LET F := (LET X := (type 2) in X) in ({X F}))%ECC.
Print example_Let2.

Notation "'Pi' x : A '->' B" := (Pi x A B) (at level 50, x at level 9, A at level 9) : ECC_scope.
Definition example_Pi := (Pi X : F -> Y)%ECC : ECCexp.
Notation "'\'  x : A  '->'  B" := (Abs x A B) (at level 50, x at level 9, A at level 9) : ECC_scope.
Definition example_Abs := (\ X: Y -> Z)%ECC : ECCexp.
Notation "'Sig' x : A '..' B" := (Sig x A B) (at level 50, x at level 1, A at level 1): ECC_scope.
Definition example_Sig := (Sig X : Y .. Z)%ECC : ECCexp.
Notation "< e1 , e2 > 'as' A" := (Pair e1 e2 A) (at level 50, e1 at level 5, e2 at level 5, A at level 5): ECC_scope.
Definition example_Pair := (< X, Y > as (Sig X : Y .. Z))%ECC : ECCexp.
Notation "'fst' e" := (Fst e) (at level 50, e at level 5): ECC_scope.
Notation "'snd' e" := (Snd e) (at level 50, e at level 5): ECC_scope.

Definition example_ycombinator := (\F:(type 3) -> ({(\X:(type 2) -> ({F {X X}})) (\X:(type 2) -> ({F {X X}}))}))%ECC.
Print example_ycombinator.

Compute subst X Y (LET Y := type 1 in X).

Goal ECC_RedClosR Empty (LET X := Y in LET Y := type 1 in X) Y.
Proof.
cut (ECC_RedR Empty (LET X := Y in LET Y := type 1 in X)%ECC (subst X (Id Y) (LET Y := type 1 in X))%ECC).
- cut (ECC_RedR Empty (subst X (Id Y) (LET Y := type 1 in X))%ECC Y). 
  + eauto.
  + cbv. apply R_Let.
- cbv. apply R_Let.
Qed.

Goal ECC_has_type Empty (fst (<Tru , Fls> as (Sig X : Bool .. Bool))) Bool.
eauto.
Qed.

Goal ECC_has_type Empty (fst (<Tru , Fls> as 
                            (Sig X : Bool .. (If X Bool (Pi Y : Bool -> Bool))))) Bool.
Proof.
eapply T_Fst. eapply T_Pair.
  - apply T_True.
  - cbv. apply T_Conv with (A := Bool) (U := Uni (uType 0)).
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
    + apply ST_Cong. apply E_Equiv with (e:= Bool).
      * auto.
      * eauto.
Unshelve. exact 1.
Qed.
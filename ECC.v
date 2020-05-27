Require Import Atom.
Require Import String Morph Var Context Relative.

(* -=ECC Definition=- *)

Inductive ECCexp {V: nat}: Type :=
  | Id (x: @atom V)
  | Uni (U: ECCuni)
  | Pi (A: ECCexp) (B: @ECCexp (S V))
  | Abs (A: ECCexp) (e: @ECCexp (S V))
  | App  (e1 e2: ECCexp)
  | Let (e1: ECCexp) (e2: @ECCexp (S V))
  | Sig (A: ECCexp) (B: @ECCexp (S V))
  | Pair (e1 e2 A: ECCexp)
  | Fst (e: ECCexp)
  | Snd (e: ECCexp)
(*   | If (e e1 e2: ECCexp) *)
  | Tru
  | Fls
  | Bool
.

Module ECCTerm <: Term.
  Definition term := @ECCexp.
  Definition unit {N}: morph (@var) N (@term) N :=
    morph_inject (@Id).

  Fixpoint kleisli {N M} (f : morph (@var) N (@term) M) V t :=
      match t with
      | Id x => f V x
      | Abs A e =>
        Abs (kleisli f V A) (nset_push (kleisli f (S V) (nset_pop e)))
      | Pi A B =>
        Pi (kleisli f V A) (nset_push (kleisli f (S V) (nset_pop B)))
      | Let e1 e2 =>
        Let (kleisli f V e1) (nset_push (kleisli f (S V) (nset_pop e2)))
      | Sig A B =>
        Sig (kleisli f V A) (nset_push (kleisli f (S V) (nset_pop B)))
      | App e1 e2 =>
        App (kleisli f V e1) (kleisli f V e2)
      | Pair e1 e2 A =>
        Pair (kleisli f V e1) (kleisli f V e2) (kleisli f V A)
      | Fst e => Fst (kleisli f V e)
      | Snd e => Snd (kleisli f V e)
      | Uni U => Uni U
      | Tru => Tru
      | Fls => Fls
      | Bool => Bool
      (*   | If (e e1 e2: ECCexp) *)
      end.

  Lemma left_identity :
    forall N M (f : morph (@var) N (@term) M) V t,
      kleisli f V (unit V t) = f V t.
  Proof. reflexivity. Qed.

  Lemma right_identity :
    forall N V (t : @term (N + V)),
      @kleisli N N unit V t = t.
  Proof.
    intros.
    inductT t; simplT; reflexivity.
  Qed.

  Lemma associativity :
      forall N M L
        (f : morph (@var) N (@term) M)
        (g : morph (@var) M (@term) L) V t,
        kleisli (fun V' t' => kleisli g V' (f V' t')) V t
        = kleisli g V (kleisli f V t).
    Proof.
      intros.
      inductT t; simplT; reflexivity.
    Qed.

  Lemma unit_extend :
    forall N V v,
      morph_extend (@unit N) V v = unit V v.
  Proof.
    intros.
    apply morph_extend_inject.
  Qed.

  Lemma kleisli_extend :
    forall N M (f : morph (@var) N (@term) M) V t,
      morph_extend (kleisli f) V t
      = kleisli (morph_extend f) V t.
  Proof.
    intros.
    inductT t; simplT; reflexivity.
  Qed.      

  Lemma extensional :
    forall N M (f g : morph (@var) N (@term) M) V t,
      (forall V t, f V t = g V t) ->
      kleisli f V t = kleisli g V t.
  Proof.
    intros.
    inductT t; simplT; auto.
  Qed.

End ECCTerm.

Module ECCRen := Renamings(ECCTerm).
Import ECCTerm.
Import ECCRen.

Inductive ctxmem:=
| Assum (A: @ECCexp 0)
| Def (e: @ECCexp 0) (A: @ECCexp 0)
.

Definition ECCenv:= @context (@ctxmem).

Inductive assumes (g: ECCenv) (x: atom) (A: ECCexp) :=
| ass :
  (has g x (Assum A)) ->
  assumes g x A
| def (e: @ECCexp 0):
  (has g x (Def e A)) ->
  assumes g x A
.

 
(* Fixpoint ECCsize (e: ECCexp) : nat :=
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
(*   | If e e1 e2 => 1 + (ECCsize e) + (ECCsize e1) + (ECCsize e2) *)
  | Tru => 1
  | Fls => 1
  | Bool => 1
end. *)

Hint Constructors ECCuni.
Hint Constructors ECCexp.

(* Lemma ECCsize_non_zero : forall e, 0 < ECCsize e.
Proof.
  induction e; simpl; omega.
Qed. *)

(* -=ECC Evaluation=- *)

(* -Lookup- *)
(* Substitution *)

(* Fixpoint FV (e: ECCexp) : atoms :=
match e with
  | Id x => singleton x
  | Uni U => empty
  | Pi x A B =>  union (FV A) (remove x (FV B))
  | Abs x A e => union (FV A) (remove  x (FV e))
  | App  e1 e2 => (union (FV e1) (FV e2))
  | Let x e1 e2 => union (FV e1) (remove  x (FV e2))
  | Sig x A B => (union (FV A) (remove  x (FV B)))
  | Pair e1 e2 A => (union (union  (FV e1) (FV e2)) (FV A))
  | Fst e => (FV e)
  | Snd e => (FV e)
(*   | If e e1 e2 => (union (union  (FV e) (FV e1)) (FV e2)) *)
  | Tru => empty
  | Fls => empty
  | Bool => empty
end. *)

(*Let's get nominal!*)
(* LET'S NOT *)
(* Fixpoint swap (x:atom) (y:atom) (t:ECCexp) : ECCexp :=
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
(*   | If e e1 e2 => (If (swap x y e) (swap x y e1) (swap x y e2)) *)
  | _ => t
  end.

Lemma swap_size_eq : forall x y t,
    ECCsize (swap x y t) = ECCsize t.
Proof.
  induction t; simpl; auto.
Qed. *)


(* If there are free variables in the substitute,
   and if the term being substituted in binds one of them,
   then we need to perform an alpha conversion of the term being substituted in
   that avoids capturing any free variables in the substitute or in the body
   of the term being substituted in. *)
(* Require Import Recdef.
Function substWork (x: atom) (arg body: ECCexp) {measure ECCsize body}:=
if (AtomSetImpl.mem x (FV body)) then 
  match body with
    | Id x' => if (x == x') then arg else body
    | Abs x' A e =>
        if (x == x')
          then (Abs x' (substWork x arg A) e)
          else let (xnew,_) := atom_fresh (union (FV arg) (FV e)) in
                      (Abs xnew (substWork x arg A) (substWork x arg (swap x' xnew e)))
    | Pi x' A B =>
        if (x == x')
          then (Pi x' (substWork x arg A) B)
          else let (xnew,_) := atom_fresh (union (FV arg) (FV B)) in
                  (Pi xnew (substWork x arg A) (substWork x arg (swap x' xnew B)))
    | Let x' A B =>
        if (x == x')
          then (Let x' (substWork x arg A) B)
          else let (xnew,_) := atom_fresh (union (FV arg) (FV B)) in
                  (Let xnew (substWork x arg A) (substWork x arg (swap x' xnew B)))
    | Sig x' A B =>
        if (x == x')
          then (Sig x' (substWork x arg A) B)
          else let (xnew,_) := atom_fresh (union (FV arg) (FV B)) in
                  (Sig xnew (substWork x arg A) (substWork x arg (swap x' xnew B)))
    | App e1 e2 => (App (substWork x arg e1) (substWork x arg e2))
    | Pair e1 e2 A => (Pair (substWork x arg e1) (substWork x arg e2) (substWork x arg A))
    | Fst e => (Fst (substWork x arg e))
    | Snd e => (Snd (substWork x arg e))
  (*   | eIf e e1 e2 => (eIf (substWork x arg e FVInArg) (substWork x arg e1 FVInArg) (substWork x arg e2 FVInArg)) *)
    | _ => body
  (*   | eSubst a b c => eSubst (substWork x arg a FVInArg) (substWork x arg b FVInArg) (substWork x arg c FVInArg) (**) *)
  end
else body.
Proof.
1-19: try (Tactics.program_simpl; cbn; omega).
1-4: try (Tactics.program_simpl; cbn; rewrite -> swap_size_eq; omega).
Qed.
 *)

(* Definition subst (x: atom) (arg body: ECCexp):= substWork x arg body. *)
(* 
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
     x `notin` (FV b2) ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (Abs x t1 b1) (Abs y t2 b2)
  | aeq_pi_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (Pi x t1 b1) (Pi x t2 b2)
  | aeq_pi_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     x `notin` (FV b2) ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (Pi x t1 b1) (Pi y t2 b2)
  | aeq_let_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (Let x t1 b1) (Let x t2 b2)
  | aeq_let_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     x `notin` (FV b2) ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (Let x t1 b1) (Let y t2 b2)
  | aeq_sig_same (x: atom) (t1 t2 b1 b2: ECCexp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (Sig x t1 b1) (Sig x t2 b2)
  | aeq_sig_diff (x y: atom) (t1 t2 b1 b2: ECCexp):
     x <> y ->
     x `notin` (FV b2) ->
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
(*   | aeq_if (e1 e2 e3 e1' e2' e3': ECCexp):
     ECC_Aeq e1 e1' ->
     ECC_Aeq e2 e2' ->
     ECC_Aeq e3 e3' ->
     ECC_Aeq (If e1 e2 e3) (If e1' e2' e3') *)
.

Hint Constructors ECC_Aeq.
 *)
(* -Step- *)

Inductive ECC_RedR : ECCenv -> ECCexp -> ECCexp -> Prop :=
  | R_ID (g: ECCenv) (x: atom) (e': ECCexp) :
    (has g x (Def e' _)) -> ECC_RedR g (Id x) e'
  | R_App (g: ECCenv) (x: atom) (A body arg: ECCexp) :
    ECC_RedR g (App (Abs x A body) arg) (subst x arg body) (*do anything with env here?*)
  | R_Fst (g: ECCenv) (e1 e2 A: ECCexp) :
    ECC_RedR g (Fst (Pair e1 e2 A)) e1
  | R_Snd (g: ECCenv) (e1 e2 A: ECCexp) :
    ECC_RedR g (Snd (Pair e1 e2 A)) e2
  | R_Let (g: ECCenv) (x: atom) (e1 e2: ECCexp) :
    ECC_RedR g (Let x e1 e2) (subst x e1 e2)  (*or here?*)
(*   | R_IfTru (g: ECCenv) (e1 e2: ECCexp) :
    ECC_RedR g (If Tru e1 e2) e1
  | R_IfFls (g: ECCenv) (e1 e2: ECCexp) :
    ECC_RedR g (If Fls e1 e2) e2 *)
.

Hint Constructors ECC_RedR.

(* Reflective Transitive Closure of step*)
Inductive ECC_RedClosR : ECCenv -> ECCexp -> ECCexp -> Prop :=
  | R_RedR (g g': ECCenv) (e e': ECCexp): (* maybe don't need this one? it follows from refl + trans*)
      ECC_RedR g e e' ->
      ECC_RedClosR g e e'
  | R_Refl (g: ECCenv) (e: ECCexp):
      ECC_RedClosR g e e
  | R_Trans (g: ECCenv) (e e' e'': ECCexp) :
      ECC_RedClosR g e e' ->
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
(*   | R_CongIf (g: ECCenv) (e e' e1 e1' e2 e2': ECCexp) :
      ECC_RedClosR g e e' ->
      ECC_RedClosR g e1 e1' ->
      ECC_RedClosR g e2 e2' ->
      ECC_RedClosR g (If e e1 e2) (If e' e1' e2') *)
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
| ST_Trans (g: ECCenv) (A A' B: ECCexp) :
  (ECC_sub_type g A A') ->
  (ECC_sub_type g A' B) ->
  (ECC_sub_type g A B)
| ST_Prop (g: ECCenv) :
  (ECC_sub_type g (Uni (uProp)) (Uni (uType 0)))
| ST_Sig (g: ECCenv) (A1 A2 B1 B2: ECCexp) (x1 x2: atom):
  (ECC_sub_type g A1 A2) ->
  (ECC_sub_type (Assum g x1 A2) B1 (subst x2 (Id x1) B2)) ->
  (ECC_sub_type g (Sig x1 A1 B1) (Sig x2 A2 B2))
.

Hint Constructors ECC_sub_type.

Inductive ECC_has_type: ECCenv -> ECCexp -> ECCexp -> Prop :=
| T_Ax_Prop (g: ECCenv) :
  ECC_Env_WF g ->
  (ECC_has_type g (Uni uProp) (Uni (uType 0)))
| T_Ax_Type (g: ECCenv) (i: nat) :
  ECC_Env_WF g ->
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
  ECC_Env_WF g ->
  (ECC_has_type g (Bool) (Uni (uType 0)))
| T_True (g: ECCenv):
  ECC_Env_WF g ->
  (ECC_has_type g (Tru) (Bool))
| T_False (g: ECCenv):
  ECC_Env_WF g ->
  (ECC_has_type g (Fls) (Bool))
(* | T_If (g: ECCenv) (B U e e1 e2: ECCexp) (x: atom):
  (ECC_has_type (Assum g x (Bool)) B U) ->
  (ECC_has_type g e (Bool)) ->
  (ECC_has_type g e1 (subst x (Tru) B)) ->
  (ECC_has_type g e2 (subst x (Fls) B)) ->
  (ECC_has_type g (If e e1 e2) (subst x e B)) *)
| T_Conv (g: ECCenv) (e A B U: ECCexp) :
  (ECC_has_type g e A) ->
  (ECC_has_type g B U) ->
  (ECC_sub_type g A B) ->
  (ECC_has_type g e B)
with
(* ECC Well-Formed Environments *)
ECC_Env_WF: ECCenv -> Prop :=
| W_Empty (g: ECCenv) :
  ECC_Env_WF Empty
| W_Assum (g: ECCenv) (x: atom) (A U: ECCexp) :
  ECC_Env_WF g ->
  ECC_has_type g A U ->
  ECC_Env_WF (Assum g x A)
| W_Def (g: ECCenv) (x: atom) (e A U: ECCexp) :
  ECC_Env_WF g ->
  ECC_has_type g A U ->
  ECC_has_type g e A ->
  ECC_Env_WF (Assum (Def g x e) x A)
.
Hint Constructors ECC_Env_WF.
Hint Constructors ECC_has_type.

(* Mutual induction Scheme *)
Scheme ECC_type_env_mut := Induction for ECC_has_type Sort Prop
with ECC_env_type_mut := Induction for ECC_Env_WF Sort Prop.

(* "induction on the mutually defined judgments ..." Scheme.
 * Think this is "simultaneous induction"? *)
Combined Scheme ECC_type_env_comb from ECC_env_type_mut, ECC_type_env_mut.

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

Notation "'P' x : A '->' B" := (Pi x A B) (at level 50, x at level 9, A at level 9) : ECC_scope.
Definition example_Pi := (P X : F -> Y)%ECC : ECCexp.
Notation "'\'  x : A  '->'  B" := (Abs x A B) (at level 50, x at level 9, A at level 9) : ECC_scope.
Definition example_Abs := (\ X: Y -> Z)%ECC : ECCexp.
Notation "'Si' x : A '..' B" := (Sig x A B) (at level 50, x at level 1, A at level 1): ECC_scope.
Definition example_Sig := (Si X : Y .. Z)%ECC : ECCexp.
Notation "< e1 , e2 > 'as' A" := (Pair e1 e2 A) (at level 50, e1 at level 5, e2 at level 5, A at level 5): ECC_scope.
Definition example_Pair := (< X, Y > as (Si X : Y .. Z))%ECC : ECCexp.
Notation "'fst' e" := (Fst e) (at level 50, e at level 5): ECC_scope.
Notation "'snd' e" := (Snd e) (at level 50, e at level 5): ECC_scope.
(* 
Definition example_ycombinator := (\F:(type 3) -> ({(\X:(type 2) -> ({F {X X}})) (\X:(type 2) -> ({F {X X}}))}))%ECC.
Print example_ycombinator.
 *)(* 
Compute subst X Y (LET Y := type 1 in X).

Goal ECC_RedClosR Empty (LET X := Y in LET Y := type 1 in X) Y.
Proof.
cut (ECC_RedR Empty (LET X := Y in LET Y := type 1 in X)%ECC (subst X (Id Y) (LET Y := type 1 in X))%ECC).
- cut (ECC_RedR Empty (subst X (Id Y) (LET Y := type 1 in X))%ECC Y). 
  + eauto.
  + cbv. apply R_Let.
- cbv. apply R_Let.
Qed.

Goal ECC_has_type Empty (fst (<Tru , Fls> as (Si X : Bool .. Bool))) Bool.
eauto.
Qed.

Goal ECC_has_type Empty (fst (<Tru , Fls> as 
                            (Si X : Bool .. (If X Bool (P Y : Bool -> Bool))))) Bool.
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
Qed. *) *)

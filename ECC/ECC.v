Require Import Atom.
Require Import String Morph Var Context Relative.

(* -=ECC Definition=- *)

Inductive exp {V: nat}: Type :=
  | Id (x: @atom V)
  | Uni (U: universe)
  | Pi (A: exp) (B: @exp (S V))
  | Abs (A: exp) (e: @exp (S V))
  | App  (e1 e2: exp)
  | Let (e1: exp) (e2: @exp (S V))
  | Sig (A: exp) (B: @exp (S V))
  | Pair (e1 e2 A: exp)
  | Fst (e: exp)
  | Snd (e: exp)
  | If (e e1 e2: exp)
  | Tru
  | Fls
  | Bool
.

Module ECCTerm <: Term.
  Definition term := @exp.
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
      | If e e1 e2 => If (kleisli f V e) (kleisli f V e1) (kleisli f V e2)
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
| Assum (A: @exp 0)
| Def (e: @exp 0) (A: @exp 0)
.

Definition env:= @context (@ctxmem).

Inductive assumes (g: env) (x: atom) (A: exp) := (* FIXME: Should x be atom or name? *)
| ass :
  (has g x (Assum A)) ->
  assumes g x A
| def (e: @exp 0):
  (has g x (Def e A)) ->
  assumes g x A
.
Hint Constructors exp.


Locate "//".
Inductive RedStep : env -> exp -> exp -> Prop :=
  | R_ID (g: env) (x: atom) (e' A: exp) :
    (has g x (Def e' A)) -> RedStep g (Id x) e'
  | R_App (g: env) (A body arg: exp) :
    RedStep g (App (Abs A body) arg) (bind arg body) (*do anything with env here?*)
  | R_Fst (g: env) (e1 e2 A: exp) :
    RedStep g (Fst (Pair e1 e2 A)) e1
  | R_Snd (g: env) (e1 e2 A: exp) :
    RedStep g (Snd (Pair e1 e2 A)) e2
  | R_Let (g: env) (e1 e2: exp) :
      RedStep g (Let e1 e2) (bind e1 e2)  (*or here?*)
  | R_IfTru (g: env) (e1 e2: exp) :
    RedStep g (If Tru e1 e2) e1
  | R_IfFls (g: env) (e1 e2: exp) :
    RedStep g (If Fls e1 e2) e2 
.

Hint Constructors RedStep.

(* Reflective Transitive Closure of step*)
Inductive RedClos : env -> exp -> exp -> Prop :=
  | R_RedR (g g': env) (e e': exp): (* maybe don't need this one? it follows from refl + trans*)
      RedStep g e e' ->
      RedClos g e e'
  | R_Refl (g: env) (e: exp):
      RedClos g e e
  | R_Trans (g: env) (e e' e'': exp) :
      RedClos g e e' ->
      RedClos g e' e'' ->
      RedClos g e e''
  | R_CongLet (g: env) (e A: exp) (e1 e2: exp) (x: name) :
      (* We need to restrict A somehow maybe  *)
      RedClos (g & x ~ Def e A) (open x e1) (open x e2) ->
      RedClos g (Let e e1) (Let e e2)
  | R_CongLam1 (g: env) (A A' e e': exp) (x: name) :
      RedClos g A A' ->
      RedClos (g & x ~ Assum A) (open x e) (open x e') ->
      RedClos g (Abs A e) (Abs A' e')
  | R_CongPi (g: env) (A A' B B': exp) (x: name) :
      RedClos g A A' ->
      RedClos (g & x ~ Assum A) (open x B) (open x B') ->
      RedClos g (Pi A B) (Pi A' B')
  | R_CongSig (g: env) (A A' B B': exp) (x: name) :
      RedClos g A A' ->
      RedClos (g & x ~ Assum A) (open x B) (open x B')->
      RedClos g (Sig A B) (Sig A' B')
  | R_CongPair (g: env) (e1 e1' e2 e2' A A': exp) :
      RedClos g e1 e1' ->
      RedClos g e2 e2' ->
      RedClos g A A'   ->
      RedClos g (Pair e1 e2 A) (Pair e1' e2' A')
  | R_CongApp (g: env) (e1 e1' e2 e2': exp) :
      RedClos g e1 e1' ->
      RedClos g e2 e2' ->
      RedClos g (App e1 e2) (App e1' e2')
  | R_CongFst (g: env) (V V': exp) :
      RedClos g V V' ->
      RedClos g (Fst V) (Fst V')
  | R_CongSnd (g: env) (V V': exp) :
      RedClos g V V' ->
      RedClos g (Snd V) (Snd V')
  | R_CongIf (g: env) (e e' e1 e1' e2 e2': exp) :
      RedClos g e e' ->
      RedClos g e1 e1' ->
      RedClos g e2 e2' ->
      RedClos g (If e e1 e2) (If e' e1' e2') 
.

Hint Constructors RedClos.


Inductive Equiv: env -> exp -> exp -> Prop :=
  | E_Equiv (g: env) (e e1 e2: exp) :
      RedClos g e1 e ->
      RedClos g e2 e ->
      Equiv g e1 e2
  | E_EquivIta1 (g: env) (e1 A e e2 e2': exp) (x: name) :
      RedClos g e1 (Abs A e) ->
      RedClos g e2 e2' ->
      Equiv (g & x ~ Assum A) (open x e) (App e2' (Id (free x))) ->
      Equiv g e1 e2
  | E_EquivIta2 (g: env) (e e1 e1' e2 A : exp) (x: name) :
      RedClos g e1 e1' ->
      RedClos g e2 (Abs A e) ->
      Equiv (g & x ~ Assum A) (App e1' (Id (free x))) (open x e) ->
      Equiv g e1 e2
(*   | E_EquivAlpha (g: env) (e1 e2: exp):
      ECC_Aeq e1 e2 ->
      Equiv g e1 e2 *)
.

Hint Constructors Equiv.

(* Typing *)

Inductive SubTypes: env -> exp -> exp -> Prop :=
| ST_Cong (g: env) (A B: exp) :
  Equiv g A B ->
  SubTypes g A B
| ST_Cum (g: env) (i: nat) :
  SubTypes g (Uni (uType i)) (Uni (uType (S i)))
| ST_Pi (g: env) (A1 A2 B1 B2: exp) (x: name) :
  (Equiv g A1 A2) ->
  (SubTypes (g & x ~ Assum A2) (open x B1) (open x B2)) ->
  (SubTypes g (Pi A1 B1) (Pi A2 B2))
| ST_Trans (g: env) (A A' B: exp) :
  (SubTypes g A A') ->
  (SubTypes g A' B) ->
  (SubTypes g A B)
| ST_Prop (g: env) :
  (SubTypes g (Uni (uProp)) (Uni (uType 0)))
| ST_Sig (g: env) (A1 A2 B1 B2: exp) (x: name):
  (SubTypes g A1 A2) ->
  (SubTypes (g & x ~ Assum A2) (open x B1) (open x B2)) ->
  (SubTypes g (Sig A1 B1) (Sig A2 B2))
.

Hint Constructors SubTypes.

Inductive Types: env -> exp -> exp -> Prop :=
| T_Ax_Prop (g: env) :
  WellFormed g ->
  (Types g (Uni uProp) (Uni (uType 0)))
| T_Ax_Type (g: env) (i: nat) :
  WellFormed g ->
  (Types g (Uni (uType i)) (Uni (uType (S i))))
| T_Var (g: env) (x: atom) (A: exp) :
  (assumes g x A) -> (* this needs adjustment *)
  (Types g (Id x) A)
| T_Let (g: env) (e e' A B: exp) (x: name):
  (Types g e A) ->
  (Types (g & x ~ Def e A) (open x e') (open x B)) ->
  (Types g (Let e e') (bind e B)) (* FIXME: review if this is correct *)
| T_Prod_Prop (g: env) (x: name) (A B: exp) (i: nat):
  (Types g A (Uni (uType i))) ->
  (Types (g & x ~ Assum A) (open x B) (Uni (uProp))) ->
  (Types g (Pi A B) (Uni (uProp)))
| T_Prod_Type (g: env) (x: name) (A B: exp) (i: nat):
  (Types g A (Uni (uType i))) ->
  (Types (g & x ~ Assum A) (open x B) (Uni (uType i))) ->
  (Types g (Pi A B) (Uni (uType i)))
| T_Lam (g: env) (x: name ) (A e B: exp) :
  (Types (g & x ~ Assum A) (open x e) (open x B)) -> (* FIXME: hmm...*)
  (Types g (Abs A e) (Pi A B))
| T_App (g: env) (x: name) (e e' A' B: exp) :
  (Types g e (Pi A' B)) ->
  (Types g e' A') ->
  (Types g (App e e') (bind e B))
| T_Sig (g: env) (x: name) (A B: exp) (i: nat) :
  (Types g A (Uni (uType i))) ->
  (Types (g & x ~ Assum A) (open x B) (Uni (uType i))) -> (* should these be the same i*)
  (Types g (Sig A B) (Uni (uType i)))
| T_Pair (g: env) (e1 e2 A B: exp):
  (Types g e1 A) ->
  (Types g e2 (bind e1 B)) ->
  (Types g (Pair e1 e2 (Sig A B)) (Sig A B))
| T_Fst (g: env) (e A B: exp):
  (Types g e (Sig A B)) ->
  (Types g (Fst e) A)
| T_Snd (g: env) (e A B: exp):
  (Types g e (Sig A B)) ->
  (Types g (Snd e) (bind (Fst e) B))
| T_Bool (g: env):
  WellFormed g ->
  (Types g (Bool) (Uni (uType 0)))
| T_True (g: env):
  WellFormed g ->
  (Types g (Tru) (Bool))
| T_False (g: env):
  WellFormed g ->
  (Types g (Fls) (Bool))
| T_If (g: env) (B: @exp 1) (U e e1 e2: exp) (x: name):
  (Types (g & x ~ Assum Bool) (open x B) U) ->
  (Types g e (Bool)) ->
  (Types g e1 (bind (Tru) B)) ->
  (Types g e2 (bind (Fls) B)) ->
  (Types g (If e e1 e2) (bind e B))
| T_Conv (g: env) (e A B U: exp) :
  (Types g e A) ->
  (Types g B U) ->
  (SubTypes g A B) ->
  (Types g e B)
with
(* ECC Well-Formed Environments *)
WellFormed: env -> Prop :=
| W_Empty :
  WellFormed ctx_empty
| W_Assum (g: env) (x: name) (A U: exp) :
  WellFormed g ->
  Types g A U ->
  WellFormed (g & x ~ Assum A)
| W_Def (g: env) (x: name) (e A U: exp) :
  WellFormed g ->
  Types g A U ->
  Types g e A ->
  WellFormed (g & x ~ Def e A)
.
Hint Constructors WellFormed.
Hint Constructors Types.

(* Mutual induction Scheme *)
Scheme type_env_mut := Induction for Types Sort Prop
with env_type_mut := Induction for WellFormed Sort Prop.

(* "induction on the mutually defined judgments ..." Scheme.
 * Think this is "simultaneous induction"? *)
Combined Scheme type_env_comb from env_type_mut, type_env_mut.

(* ECC Notation *)

Bind Scope ECC_scope with exp.
Bind Scope ECC_scope with universe.
Bind Scope ECC_scope with env.
Delimit Scope ECC_scope with ECC.
Coercion Id: atom >-> exp.

Notation "'type' x" := (Uni (uType x)) (at level 50):  ECC_scope.
Notation "'prop'" := (Uni uProp) (at level 50):  ECC_scope.
Notation "{ e1 e2 }" := (App e1 e2) (at level 50,e1 at level 9):  ECC_scope.
Notation "'LET' x ':=' A 'in' B" := (Let A B) (at level 50, format "'[v' 'LET'  x  ':='  A '/' 'in' '['  B ']' ']'") : ECC_scope.
Notation "'P' '_' : A '->' B" := (Pi A B) (at level 50, A at level 9) : ECC_scope.
Notation "'\'  '_' : A  '->'  B" := (Abs A B) (at level 50,  A at level 9) : ECC_scope.
Notation "'Si' '_' : A '..' B" := (Sig A B) (at level 50, A at level 1): ECC_scope.
Notation "< e1 , e2 > 'as' A" := (Pair e1 e2 A) (at level 50, e1 at level 5, e2 at level 5, A at level 5): ECC_scope.
Notation "'fst' e" := (Fst e) (at level 50, e at level 5): ECC_scope.
Notation "'snd' e" := (Snd e) (at level 50, e at level 5): ECC_scope.

Example ex_fst: Types ctx_empty (fst (< Tru, Fls> as (Si _ : Bool .. Bool)))%ECC Bool.
Proof.
eapply T_Fst. auto.
Qed.

Require Import Lia.
Fixpoint size {V: nat} (e: @exp V) : nat :=
  match e with
  | Id _ => 1
  | Uni _ => 1
  | Pi A B => 1 + (size A) + (size B)
  | Abs A e => 1 + (size A) + (size e)
  | App e1 e2 => 1 + (size e1) + (size e2)
  | Let e1 e2 => 1 + (size e1) + (size e2)
  | Sig A B => 1 + (size A) + (size B)
  | Pair e1 e2 A => 1 + (size e1) + (size e2) + (size A)
  | Fst e => 1 + (size e)
  | Snd e => 1 + (size e)
  | If e e1 e2 => 1 + (size e) + (size e1) + (size e2) 
  | Tru => 1
  | Fls => 1
  | Bool => 1
end.

Lemma size_non_zero : forall V e, 0 < @size V e.
Proof.
  induction e; simpl; lia.
Qed.

Lemma size_open_id : forall {V: nat} (e: @exp (1 + V)) x, @size (V) (open x e) = @size (1 + V) e.
Proof. intros. 
  inductT e; induction V0; cbn; try easy; try (rewrite IHe1; try easy; rewrite IHe2; try easy; try (rewrite IHe3; try easy)).
  all: ( rewrite IHe; try easy).
Qed.

Lemma size_close_id : forall {V: nat} (e: @exp (V)) x, @size (1 + V) (close x e) = @size (V) e.
Proof. intros. induction e; names; auto.
Qed.

Lemma size_wk_id : forall {V: nat} (e: @exp (V)), @size (1 + V) (wk e) = @size (V) e.
Proof. intros. induction e; names; auto.
Qed.

Hint Resolve size_open_id size_close_id size_wk_id.

(* Definition example_Type := (type 3)%ECC: exp.
Definition example_Prop := (prop)%ECC: exp.
Definition example_App := { X Y }%ECC: exp.
Definition example_Let := (LET X := Y in Z)%ECC : exp.
Print example_Let.
Definition F:= fresh (X::Y::Z::nil).
Definition example_Let2 := (LET X := (type 3) in LET F := (LET X := (type 2) in X) in ({X F}))%ECC.
Print example_Let2.
Definition example_Pi := (P X : F -> Y)%ECC : exp.
Definition example_Abs := (\ X: Y -> Z)%ECC : exp.
Definition example_Sig := (Si X : Y .. Z)%ECC : exp.
Definition example_Pair := (< X, Y > as (Si X : Y .. Z))%ECC : exp. *)

(* 
Definition example_ycombinator := (\F:(type 3) -> ({(\X:(type 2) -> ({F {X X}})) (\X:(type 2) -> ({F {X X}}))}))%ECC.
Print example_ycombinator.
 *)(* 
Compute subst X Y (LET Y := type 1 in X).

Goal RedClos Empty (LET X := Y in LET Y := type 1 in X) Y.
Proof.
cut (RedStep Empty (LET X := Y in LET Y := type 1 in X)%ECC (subst X (Id Y) (LET Y := type 1 in X))%ECC).
- cut (RedStep Empty (subst X (Id Y) (LET Y := type 1 in X))%ECC Y). 
  + eauto.
  + cbv. apply R_Let.
- cbv. apply R_Let.
Qed.



Goal Types Empty (fst (<Tru , Fls> as 
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
Qed. *)




(* -=ECC Evaluation=- *)

(* -Lookup- *)
(* Substitution *)

(* Fixpoint FV (e: exp) : atoms :=
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
(* Fixpoint swap (x:atom) (y:atom) (t:exp) : exp :=
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
    size (swap x y t) = size t.
Proof.
  induction t; simpl; auto.
Qed. *)


(* If there are free variables in the substitute,
   and if the term being substituted in binds one of them,
   then we need to perform an alpha conversion of the term being substituted in
   that avoids capturing any free variables in the substitute or in the body
   of the term being substituted in. *)
(* Require Import Recdef.
Function substWork (x: atom) (arg body: exp) {measure size body}:=
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

(* Definition subst (x: atom) (arg body: exp):= substWork x arg body. *)
(* 
Inductive ECC_Aeq : exp -> exp -> Prop :=
  | aeq_id (e: exp):
    ECC_Aeq e e
  | aeq_var (x: atom):
     ECC_Aeq (Id x) (Id x)
  | aeq_abs_same (x: atom) (t1 t2 b1 b2: exp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (Abs x t1 b1) (Abs x t2 b2)
  | aeq_abs_diff (x y: atom) (t1 t2 b1 b2: exp):
     x <> y ->
     x `notin` (FV b2) ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (Abs x t1 b1) (Abs y t2 b2)
  | aeq_pi_same (x: atom) (t1 t2 b1 b2: exp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (Pi x t1 b1) (Pi x t2 b2)
  | aeq_pi_diff (x y: atom) (t1 t2 b1 b2: exp):
     x <> y ->
     x `notin` (FV b2) ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (Pi x t1 b1) (Pi y t2 b2)
  | aeq_let_same (x: atom) (t1 t2 b1 b2: exp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (Let x t1 b1) (Let x t2 b2)
  | aeq_let_diff (x y: atom) (t1 t2 b1 b2: exp):
     x <> y ->
     x `notin` (FV b2) ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (Let x t1 b1) (Let y t2 b2)
  | aeq_sig_same (x: atom) (t1 t2 b1 b2: exp):
     ECC_Aeq t1 t2 -> 
     ECC_Aeq b1 b2 ->
     ECC_Aeq (Sig x t1 b1) (Sig x t2 b2)
  | aeq_sig_diff (x y: atom) (t1 t2 b1 b2: exp):
     x <> y ->
     x `notin` (FV b2) ->
     ECC_Aeq b1 (swap y x b2) ->
     ECC_Aeq t1 t2 ->
     ECC_Aeq (Sig x t1 b1) (Sig y t2 b2)
  | aeq_app (t1 t2 t1' t2': exp):
     ECC_Aeq t1 t1' -> ECC_Aeq t2 t2' ->
     ECC_Aeq (App t1 t2) (App t1' t2')
  | aeq_pair (t1 t2 t1' t2' A A': exp):
     ECC_Aeq t1 t1' -> ECC_Aeq t2 t2' ->
     ECC_Aeq A A' ->
     ECC_Aeq (Pair t1 t2 A) (Pair t1' t2' A')
  | aeq_Fst (e e': exp):
     ECC_Aeq e e' ->
     ECC_Aeq (Fst e) (Fst e')
  | aeq_Snd (e e': exp):
     ECC_Aeq e e' ->
     ECC_Aeq (Snd e) (Snd e')
(*   | aeq_if (e1 e2 e3 e1' e2' e3': exp):
     ECC_Aeq e1 e1' ->
     ECC_Aeq e2 e2' ->
     ECC_Aeq e3 e3' ->
     ECC_Aeq (If e1 e2 e3) (If e1' e2' e3') *)
.

Hint Constructors ECC_Aeq.
 *)
(* -Step- *)

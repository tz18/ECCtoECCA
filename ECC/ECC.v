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
Hint Constructors exp.

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

(* -=ECC Environments=- *)

Inductive ctxmem :=
| Assum (A: @exp 0)
| Def (e: @exp 0) (A: @exp 0).

Module envParams <: ContextParams.
  Definition A:= ctxmem.

  Definition trm:= @exp 0.
  Definition apply r (t: A) :=
  match t with
  | Assum A => Assum ([r] A)
  | Def e A => Def ([r] e) ([r] A)
  end.
  
  Lemma shift_commutes_total: 
  forall r (rn: total r) x (b: A), 
  apply (r,, ^ x)%ren b = apply (^ x)%ren (apply r b).
  Proof. intros; destruct b; cbn; names; auto. Qed.

  Lemma rw_rename_shift_total:
  forall r (rn: total r) x y (c: A), 
  apply (r,, ^ y)%ren c = apply (r,, y <- x)%ren (apply (^ x)%ren c).
  Proof. intros; destruct c; cbn; names; auto. Qed.

  Lemma id_id:
  forall a, apply r_id a = a.
  Proof. intros; destruct a; cbn; names; auto. Qed.

End envParams.

Module env := Context(envParams).
Import envParams. Import env.
Definition env:= context.

Definition assumes (g: env) (x: atom) (A: exp) :=
(has g x (Assum A)) \/ (exists (e: exp), (has g x (Def e A))).
Hint Unfold assumes.

Bind Scope ECC_scope with exp.
Bind Scope ECC_scope with env.
Delimit Scope ECC_scope with ECC.

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
Reserved Notation "g '⊢' a ':' b" (at level 250, a at level 99).
Reserved Notation "'⊢' g" (at level 250).
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
  (Types (g & x ~ Assum A) (open x e) (open x B)) ->
  (Types g (Abs A e) (Pi A B))
| T_App (g: env) (x: name) (e e' A' B: exp) :
  (Types g e (Pi A' B)) ->
  (Types g e' A') ->
  (Types g (App e e') (bind e B))
| T_Sig (g: env) (x: name) (A B: exp) (i: nat) :
  (Types g A (Uni (uType i))) ->
  (Types (g & x ~ Assum A) (open x B) (Uni (uType i))) -> 
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
where "g '⊢' a ':' b" := (Types g a b) : ECC_scope
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
where "'⊢' g" := (WellFormed g) : ECC_scope
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

Notation "'type' x" := (Uni (uType x)) (at level 50):  ECC_scope.
Notation "'prop'" := (Uni uProp) (at level 50):  ECC_scope.
Notation "{ e1 e2 }" := (App e1 e2) (at level 50,e1 at level 9):  ECC_scope.
Notation "'LET' A 'in' B" := (Let A B) (at level 50) : ECC_scope.
Notation "'Π': A '->' B" := (Pi A B) (at level 50, A at level 9) : ECC_scope.
Notation "'λ' : A  '->'  B" := (Abs A B) (at level 50,  A at level 9) : ECC_scope.
Notation "'Σ' : A '..' B" := (Sig A B) (at level 50, A at level 1): ECC_scope.
Notation "< e1 , e2 > 'as' A" := (Pair e1 e2 A) (at level 50, e1 at level 5, e2 at level 5, A at level 5): ECC_scope.
Notation "'fst' e" := (Fst e) (at level 50, e at level 5): ECC_scope.
Notation "'snd' e" := (Snd e) (at level 50, e at level 5): ECC_scope.

Example ex_fst: Types ctx_empty (fst (< Tru, Fls> as (Σ : Bool .. Bool)))%ECC Bool.
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

(*=============================
========Induction principle====
===============================*)

Inductive Vclosed : @term 0 -> Set :=
  | vc_Id (X: @atom 0) : Vclosed (Id X)
  | vc_Uni (U: universe) : Vclosed (Uni U)
  | vc_Pi (A: exp) (B: @exp 1) : Vclosed A -> (forall x, Vclosed (open x B)) -> Vclosed (Pi A B)
  | vc_Abs (A: exp) (B: @exp 1) : Vclosed A -> (forall x, Vclosed (open x B)) -> Vclosed (Abs A B)
  | vc_Sig (A: exp) (B: @exp 1) : Vclosed A -> (forall x, Vclosed (open x B)) -> Vclosed (Sig A B)
  | vc_Pair (v1 v2: exp) (A: exp) : Vclosed v1 -> Vclosed v2 -> Vclosed A -> Vclosed (Pair v1 v2 A)
  | vc_Tru : Vclosed (Tru)
  | vc_Fls : Vclosed (Fls)
  | vc_Bool: Vclosed (Bool)
  | vc_Let (A: exp) (B: @exp 1) : Vclosed A -> (forall n, Vclosed (open n B)) -> Vclosed (Let A B)
  | vc_If (v: exp) (e1 e2: exp) : Vclosed v -> Vclosed e1 -> Vclosed e2 -> Vclosed (If v e1 e2)
  | vc_App (v1 v2: exp) : Vclosed v1 -> Vclosed v2 -> Vclosed (App v1 v2)
  | vc_Fst (v: exp) : Vclosed v -> Vclosed (Fst v)
  | vc_Snd (v: exp) : Vclosed v -> Vclosed (Snd v).

Check Vclosed_ind.

Fixpoint Vclosedk (V : nat) : @term V -> Set :=
  match V with
  | 0 => fun t => Vclosed t
  | S V => fun t => forall n, Vclosedk V (open n t)
  end.

Fixpoint always_Vclosedk {V : nat} (t : term) {struct t} : Vclosedk V t :=
  match t with
  | Id x =>
    let fix go {V} : forall (x : @atom V), Vclosedk V (Id x) :=
      match V with
      | 0 => vc_Id
      | S V => fun v n => go _
      end
    in go x
  | Uni U =>
    let fix go {V} : forall (U : universe), Vclosedk V (Uni U) :=
      match V with
      | 0 => vc_Uni
      | S V => fun v n => go _
      end
    in go U
  | Pi A B =>
    let fix go {V} : forall A B, Vclosedk (V) A ->
                      Vclosedk (S V) B ->
                      Vclosedk V (Pi A B) :=
      match V with
      | 0 => vc_Pi
      | S V => fun _ _ vca vcb a=> go _ _ (vca a) (vcb a)
      end
    in go _ _ (always_Vclosedk A) (always_Vclosedk B)
  | Abs A B =>
    let fix go {V} : forall A B, Vclosedk (V) A ->
                      Vclosedk (S V) B ->
                      Vclosedk V (Abs A B) :=
      match V with
      | 0 => vc_Abs
      | S V => fun _ _ vca vcb a=> go _ _ (vca a) (vcb a)
      end
    in go _ _ (always_Vclosedk A) (always_Vclosedk B)
  | Sig A B =>
    let fix go {V} : forall A B, Vclosedk (V) A ->
                      Vclosedk (S V) B ->
                      Vclosedk V (Sig A B) :=
      match V with
      | 0 => vc_Sig
      | S V => fun _ _ vca vcb a=> go _ _ (vca a) (vcb a)
      end
    in go _ _ (always_Vclosedk A) (always_Vclosedk B)
  | Pair v1 v2 A =>
    let fix go {V} : forall v e1 e2, Vclosedk V v ->
                                     Vclosedk V e1 ->
                                     Vclosedk V e2 ->
                                     Vclosedk V (Pair v e1 e2) :=
      match V with
      | 0 => vc_Pair
      | S V => fun _ _ _ vv1 vv2 va a => go _ _ _ (vv1 a) (vv2 a) (va a)
      end
    in go _ _ _ (always_Vclosedk v1) (always_Vclosedk v2) (always_Vclosedk A)
  | Tru =>
    let fix go {V} : Vclosedk V _ :=
      match V with 0 => vc_Tru | S V => fun _ => go end in
    go
  | Fls =>
    let fix go {V} : Vclosedk V _ :=
      match V with 0 => vc_Fls | S V => fun _ => go end in
    go
  | Bool =>
    let fix go {V} : Vclosedk V _ :=
      match V with 0 => vc_Bool | S V => fun _ => go end in
    go
  | Let A B =>
    let fix go {V} : forall A B, Vclosedk (V) A ->
                      Vclosedk (S V) B ->
                      Vclosedk V (Let A B) :=
      match V with
      | 0 => vc_Let
      | S V => fun _ _ vca vcb a=> go _ _ (vca a) (vcb a)
      end
    in go _ _ (always_Vclosedk A) (always_Vclosedk B)
  | If v e1 e2 =>
    let fix go {V} : forall v e1 e2, Vclosedk V v ->
                                     Vclosedk V e1 ->
                                     Vclosedk V e2 ->
                                     Vclosedk V (If v e1 e2) :=
      match V with
      | 0 => vc_If
      | S V => fun _ _ _ vv ve1 ve2 a => go _ _ _ (vv a) (ve1 a) (ve2 a)
      end
    in go _ _ _ (always_Vclosedk v) (always_Vclosedk e1) (always_Vclosedk e2)
  | App f e  =>
    let fix go {V} : forall f e, Vclosedk V f ->
                                 Vclosedk V e ->
                                 Vclosedk V (App f e) :=
      match V with
      | 0 => vc_App
      | S V => fun _ _ vf ve a => go _ _ (vf a) (ve a)
      end
    in go _ _ (always_Vclosedk f) (always_Vclosedk e)
  | Fst v =>
    let fix go {V} : forall v, Vclosedk V v ->
                                 Vclosedk V (Fst v) :=
      match V with
      | 0 => vc_Fst
      | S V => fun _ vv a => go _ (vv a)
      end
    in go _ (always_Vclosedk v)
  | Snd v =>
    let fix go {V} : forall v, Vclosedk V v ->
                                 Vclosedk V (Snd v) :=
      match V with
      | 0 => vc_Snd
      | S V => fun _ vv a => go _ (vv a)
      end
    in go _ (always_Vclosedk v)
end.

Check Vclosed_ind.
 
Definition term_ind
             (P : @exp 0 -> Prop)
             (IDD : forall (v : atom), P (Id v))
             (UNI : forall (U : universe), P (Uni U))
             (TRU : P (Tru))
             (FLS : P (Fls))
             (BOO : P (Bool))
             (ABS : forall (A B : exp),
                 P (A) ->
                 (forall (n : name), P (open n B)) ->
                 P (Abs A B))
             (PIE : forall (A B : exp),
                 P (A) ->
                 (forall (n : name), P (open n B)) ->
                 P (Pi A B))
             (SIG : forall (A B : exp),
                 P (A) ->
                 (forall (n : name), P (open n B)) ->
                 P (Sig A B))
             (LeT : forall (A B : exp),
                 P (A) ->
                 (forall (n : name), P (open n B)) ->
                 P (Let A B))
             (APP : forall (f e : exp), P f -> P e -> P (App f e))
             (PAI : forall (v1 v2 A : exp), P v1 -> P v2 -> P A -> P (Pair v1 v2 A))
             (IFF : forall (v e1 e2 : exp), P v -> P e1 -> P e2 -> P (If v e1 e2))
             (FST : forall (v : exp), P v -> P (Fst v))
             (SND : forall (v : exp), P v -> P (Snd v))
             (tm : exp) : P tm :=
    Vclosed_ind (fun tm _ => P tm)
       IDD UNI
       (fun a b _ Ha _ Hb => PIE a b Ha Hb)
       (fun a b _ Ha _ Hb => ABS a b Ha Hb)
       (fun a b _ Ha _ Hb => SIG a b Ha Hb)
       (fun v1 v2 a _ Hv1 _ Hv2 _ Ha => PAI v1 v2 a Hv1 Hv2 Ha)
       TRU FLS BOO
       (fun a b _ Ha _ Hb => LeT a b Ha Hb)
       (fun v e1 e2 _ Hv _ He1 _ He2 => IFF v e1 e2 Hv He1 He2)
       (fun f e _ F _ E => APP f e F E)
       (fun v _ V => FST v V)
       (fun v _ V => SND v V)
       tm (always_Vclosedk tm).

Check Vclosed_ind.
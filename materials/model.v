(*
 Consistency of target
 ===

 Suppose we have a language ECCᴬ, which is ECC with dependent case on sums
 extended with the following.

 Reduction rule:
   subst (v = v) e → e [E-Refl]
   case (injᵢ e) x₁.e₁; x₂.e₂ → eᵢ[e/xᵢ]

 (No other reduction rules are required if equivalences v₁ = v₁ ∈ Γ are
 restricted to values, as they will be in ANF)

 Typing rules:
   Γ,x : A ⊢ B : Type
   Γ ⊢ eᵢ : A
   Γ ⊢ e : B[e₁/x]
   v₁ = v₂ ∈ Γ
   ---------------------- [T-Subst]
   Γ ⊢ subst (v₁ = v₂) e : B[e₂/x]


   Γ, y : A₁ + A₂ ⊢ C : Type
   Γ ⊢ e : A₁ + A₂
   Γ, xᵢ : Aᵢ, injᵢ xᵢ = e ⊢ eᵢ : C[injᵢ xᵢ/y]
   ------------------------------- [T-Case]
   Γ ⊢ case e x₁.e₁; x₂.e₂ : C[e/y]

 Equivalence rules:
               Γ ⊢ e₁ ≡ e₂
    ---------------------------
    Γ ⊢ subst (inj₁ x₁ = e) e₁ ≡ e₂

      true = false ∈ Γ
    -----------------
       Γ ⊢ e₁ ≡ e₂

Important Equivalence:
    E[case e x₁.e₁; x₂.e₂] : A ≡ case e.x₁.E[subst (inj₁ x₁ = e) e₁];
                                        x₂.E[subst (inj₂ x₂ = e) e₂] : A

    This doesn't need to be a rule, as we can prove it holds as a theorem in
    ECCᴬ. The equivalence is easy; the fact that both sides are
    well-typed is the hard part.


 The following definitions give a model in CIC of ECCᴬ.

 Implement [T-Subst] and [T-Case] in CIC as:

   〚subst (A = B) e〛 = (subst p 〚e〛), where `subst` is defined below
                                    where p : 〚A〛 = 〚B〛 ∈ 〚Γ〛

   〚case e x₁.e₂; x₂.e₂〛 = (case 〚e〛 x₁.(λ (p : (inj₁ x₁ = 〚e〛)).
                                          (subst (case_eta1 ...) 〚e₁〛);
                                   x₂.(λ (p : (inj₂ x₂ = 〚e〛)).
                                          (subst (case_eta2 ...) 〚e₂〛))
                           (refl 〚e〛)

 The central proof that this is a model are given by `case_commutes`
 `subst_equiv`, defined below.

 Note that we prove the above equivalence as a propositional equality in Coq,
 but we require definitional equality in ECC_coe.
 Thus this Coq proof, strictly speaking, only yields a model of ECCᴬ in CIC
 when we add (a weak form of) equivalence reflection to CIC.

 Reliance on equivalence reflection is inconsistent with the homotopy type
 theory.
 However, we conjecture that ECCᴬ doesn't actually rely on equivalence
 reflection; this is merely a limitation in how we've developed the model in
 Coq.
 The property we really care about is that reduction is blocked until a coercion
 between the two types is witnessed, thus ensuring termination when full
 reduction takes place under possibly inconsistent assumptions.
 We do not even require the that coercion be the identity---it just so happens
 that, in the case of ANF for ECC, this is sufficient.
 This idea that full reduction must be blocked under inconsistent assumptions is
 discussed at length in \citet{scherer2015:absurdity}, which goes on to develop
 a non-dependent calculus with that very goal.
 Other dependently type calculi use explicit coercions that have computational
 content, such as \citet{weirich2017,doorn2013,geuvers2008}.

 Note that this model is slightly different than what we present in the paper; I
 use sums and case instead of booleans and if.
 This is not an important difference, since with Π and Σ, they can express each
 other.
 *)

Inductive Either (A : Set) (B : Set) : Set :=
| inj1 : A -> Either A B
| inj2 : B -> Either A B.

(* subst replaces a term x in some type C with an equal term y. *)
Definition subst {A} {x : A} {y : A} {C : A -> Type} (p : x = y) (e : C x) : C y.
Proof.
  rewrite <- p; exact e.
Defined.

Definition subst_equiv {A} {x : A} {y : A} {C : A -> Type} (p : x = y) (e₁ : C x) (e₂ : C x) (p1 : e₁ = e₂) : (subst p e₁) = e₂.
Proof.
  destruct p; simpl. exact p1.
Defined.

Definition absurd_equiv {A : Set} {B : Set} {x : A} {y : B} {C : Type} (p : inj1 _ _ x = inj2 _ _ y) (e1 : C) (e2 : C) : e1 = e2.
Proof.
  inversion p.
Defined.

(* Essentially, an η law for case, which relies on an explicit equality.
   The first branch of a case is equivalent to case analysis on a term equal to
   the first projection.
   It doesn't quite look like an eta rule due to homogeneous equality.
   See case_eta1_heq for the expected statement, but which is incomapatible with
   univalence.
 *)
Theorem case_eta1
  {A B} (e : Either A B)
  (C : (Either A B) -> Type)
  (e1 : forall (x1 : A), (C (inj1 _ _ x1)))
  (e2 : forall (x2 : B), (C (inj2 _ _ x2)))
  (D : (C e) -> Type)
  (x1 : A)
  (p : inj1 A B x1 = e) :
  (subst p (e1 x1)) =
  (match e as e0 return (C e0) with
     | inj1 _ _ x1 => (e1 x1)
     | inj2 _ _ x2 => (e2 x2)
     end).
Proof.
  destruct p; reflexivity.
Defined.

(* Essentially, an η law for case, which relies on an explicit equality.
   The second branch of a case is equivalent to case analysis on a term equal to
   the second projection.
 *)
Theorem case_eta2
  {A B} (e : Either A B)
  (C : (Either A B) -> Type)
  (e1 : forall (x1 : A), (C (inj1 _ _ x1)))
  (e2 : forall (x2 : B), (C (inj2 _ _ x2)))
  (D : (C e) -> Type)
  (x2 : B)
  (p : inj2 A B x2 = e) :
  (subst p (e2 x2)) =
  (match e as e0 return (C e0) with
     | inj1 _ _ x1 => (e1 x1)
     | inj2 _ _ x2 => (e2 x2)
     end).
Proof.
  destruct p; reflexivity.
Defined.

(* An evaluation context (represented by a function `f`) commutes with dependent
   case on sums, up to some explicit conversions between the dependent types.
   Note that the argument type of `f` is the same as the dependent match, and
   the result type of `f` depends on the argument.
   Both of these are necessary to capture an arbitrary dependent evaluation context.
 *)
Definition case_commutes {A B} (e : Either A B)
        (C : (Either A B) -> Type)
        (e1 : forall (x1 : A), (C (inj1 _ _ x1)))
        (e2 : forall (x2 : B), (C (inj2 _ _ x2)))
        {D}
        (f : (forall (x : (C e)), (D x))) :
        (f (match e as e0 return (C e0) with
                  | inj1 _ _ x1 => (e1 x1)
                  | inj2 _ _ x2 => (e2 x2)
            end))
        =
        ((match e as e0 return (forall (p : e0 = e), D (match e as e0 return (C e0) with
                  | inj1 _ _ x1 => (e1 x1)
                  | inj2 _ _ x2 => (e2 x2)
            end)) with
          | inj1 _ _ x1 =>
            (fun (p : (inj1 A B x1) = e) =>
               (subst (C:=D) (case_eta1 e C e1 e2 D x1 p) (f (subst p (e1 x1)))))
          | inj2 _ _ x2 =>
            (fun (p : (inj2 A B x2) = e) =>
               (subst (C:=D) (case_eta2 e C e1 e2 D x2 p) (f (subst p (e2 x2)))))
          end) eq_refl).
Proof.
  destruct e; reflexivity.
Defined.

Require Import Program.
(* The expected statement of eta1 *)
Theorem case_eta1_heq
  {A B} (e : Either A B)
  (C : (Either A B) -> Type)
  (e1 : forall (x1 : A), (C (inj1 _ _ x1)))
  (e2 : forall (x2 : B), (C (inj2 _ _ x2)))
  (D : (C e) -> Type)
  (x1 : A)
  (p : inj1 A B x1 = e) :
  (e1 x1) ~=
  (match e as e0 return (C e0) with
     | inj1 _ _ x1 => (e1 x1)
     | inj2 _ _ x2 => (e2 x2)
     end).
Proof.
  destruct p; reflexivity.
Defined.

Theorem case_eta2_heq
  {A B} (e : Either A B)
  (C : (Either A B) -> Type)
  (e1 : forall (x1 : A), (C (inj1 _ _ x1)))
  (e2 : forall (x2 : B), (C (inj2 _ _ x2)))
  (D : (C e) -> Type)
  (x2 : B)
  (p : inj2 A B x2 = e) :
  (e2 x2) ~=
  (match e as e0 return (C e0) with
     | inj1 _ _ x1 => (e1 x1)
     | inj2 _ _ x2 => (e2 x2)
     end).
Proof.
  destruct p; reflexivity.
Defined.

Definition subst_equiv_heq {A} {x : A} {y : A} {C : A -> Type} (p : x = y) (e₁ : C x) (e₂ : C y) (p1 : e₁ ~= e₂) : (subst p e₁) ~= e₂.
Proof.
  destruct p; simpl. exact p1.
Defined.

Definition absurd_equiv_heq {A : Set} {B : Set} {x : A} {y : B} {C : Type} {D : Type} (p : inj1 _ _ x = inj2 _ _ y) (e1 : C) (e2 : D) : e1 ~= e2.
Proof.
  inversion p.
Defined.

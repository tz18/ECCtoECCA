Require Export Atom.
Require Import String Morph Var Context Relative.
(* 
=====================================
=======--ECCA Definition--=========== 
=====================================
*)

Declare Scope ECCA_scope.
Delimit Scope ECCA_scope with ECCA.

(* Restricted ECCA, used in computing *)

Inductive ECCAval {V: nat}: Type :=
  | Id (x: @atom V)
  | Uni (U: ECCuni)
  | Pi (A: ECCAconf) (B: @ECCAconf (S V))
  | Abs (A: ECCAconf) (B: @ECCAconf (S V))
  | Sig (A: ECCAconf) (B: @ECCAconf (S V))
  | Pair (v1 v2: ECCAval) (A: @ECCAconf V)
  | Tru
  | Fls
  | Bool
with
ECCAconf {V: nat}: Type :=
  | Comp (e: ECCAcomp)
  | Let (A: ECCAcomp) (B: @ECCAconf (S V))
  | If (v: ECCAval) (m1 m2: ECCAconf)
with
ECCAcomp {V: nat}: Type :=
  | App (v1 v2: ECCAval)
  | Val (v: ECCAval)
  | Fst (v: ECCAval)
  | Snd (v: ECCAval)
.

(* Mutual induction Scheme *)
Scheme ECCA_val_conf_mut := Induction for ECCAval Sort Prop
with ECCA_conf_comp_mut := Induction for ECCAconf Sort Prop
with ECCA_comp_val_mut := Induction for ECCAcomp Sort Prop.

Combined Scheme ECCA_val_conf_comp_comb from ECCA_val_conf_mut, ECCA_conf_comp_mut, ECCA_comp_val_mut.

(* Fixpoint open_val a {V} (t: @ECCAval (S V)):=
match t with 
  | Id x => Id (openv a v)
  | Pair v1 v2 A => Pair (open_val a v1) (open_val a v2) (open_conf a A)
  | Pi A B(A: ECCAconf) (B: @ECCAconf (S V)) => Pi (open_conf a A) (open_conf a B)
  | Abs A B(A: ECCAconf) (B: @ECCAconf (S V)) => Abs (open_conf a A) (open_conf a B)
  | Sig A B(A: ECCAconf) (B: @ECCAconf (S V)) => Sig (open_conf a A) (open_conf a B)
  | (Uni U) as v | Tru as v | Fls as v | Bool as v => v
end
with 
open_comp a {V} (t: @ECCAcomp (S V)) :=
match
  | App v1 v2 => App (open_val a v1) (open_val a v2)
  | Val v => Val (open_val a v)
  | Fst v => Fst (open_val a v)
  | Snd v => Snd (open_val a v)
end
open_conf a {V} (t: @ECCAconf (S V)) :=
match
  | Comp e => Comp (open_comp a e)
  | Let A B => Let (open_comp a A) (open_comp a B)
end *)


Hint Constructors ECCAval. 
Coercion Id: atom >-> ECCAval.
Bind Scope ECCA_scope with ECCAval.
Bind Scope ECCA_scope with ECCAconf.
Bind Scope ECCA_scope with ECCAcomp.


Inductive ECCAexp {V: nat}: Type :=
  | eId (x: @atom V)
  | eUni (U: ECCuni)
  | ePi (A: ECCAexp) (B: @ECCAexp (S V))
  | eAbs (A: ECCAexp) (B: @ECCAexp (S V))
  | eSig (A: ECCAexp) (B: @ECCAexp (S V))
  | ePair (v1 v2: ECCAexp) (A: ECCAexp)
  | eTru
  | eFls
  | eBool
  | eLet (A: ECCAexp) (B: @ECCAexp (S V))
  | eIf (v: ECCAexp) (e1 e2: ECCAexp) 
  | eApp (v1 v2: ECCAexp)
  | eFst (v: ECCAexp)
  | eSnd (v: ECCAexp)
(*   | eSubst (x arg body: ECCAexp) *)
.

(* Approach: If we have an ECCAexp with a proof
 that we can get an ECCAconf out of it, we should be able to
 extract the ECCAconf. Three fundamental naming operations cannot break ANF:
 wk, open, and close. The only operation that could potentially break ANF is bind.
 Let's apply these constructors by operating over the ECCAexp,
 preserving the proof that it is ANF,
 and extracting the ECCAconf back after.*)

Hint Constructors ECCAexp.

Module ECCATerm <: Term.
  Definition term := @ECCAexp.
  Definition unit {N}: morph (@var) N (@term) N :=
    morph_inject (@eId).

  Fixpoint kleisli {N M} (f : morph (@var) N (@term) M) V t :=
      match t with
      | eId x => f V x
      | eAbs A e =>
        eAbs (kleisli f V A) (nset_push (kleisli f (S V) (nset_pop e)))
      | ePi A B =>
        ePi (kleisli f V A) (nset_push (kleisli f (S V) (nset_pop B)))
      | eLet e1 e2 =>
        eLet (kleisli f V e1) (nset_push (kleisli f (S V) (nset_pop e2)))
      | eSig A B =>
        eSig (kleisli f V A) (nset_push (kleisli f (S V) (nset_pop B)))
      | eApp e1 e2 =>
        eApp (kleisli f V e1) (kleisli f V e2)
      | ePair e1 e2 A =>
        ePair (kleisli f V e1) (kleisli f V e2) (kleisli f V A)
      | eIf v e1 e2 =>
        eIf (kleisli f V v) (kleisli f V e1) (kleisli f V e2)
      | eFst e => eFst (kleisli f V e)
      | eSnd e => eSnd (kleisli f V e)
      | eUni U => eUni U
      | eTru => eTru
      | eFls => eFls
      | eBool => eBool
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

End ECCATerm.

Module ECCARen := Renamings(ECCATerm).
Export ECCATerm.
Export ECCARen.


(* 
============================================================
=======--Moving from restricted to unrestricted--=========== 
============================================================
*)

Fixpoint flattenECCAval {V: nat} (v: @ECCAval V): @ECCAexp V :=
match v with
  | Id x => eId x
  | Uni U => eUni U
  | Pi A B => ePi (flattenECCAconf A) (flattenECCAconf B) 
  | Abs A B => eAbs (flattenECCAconf A) (flattenECCAconf B)
  | Sig A B => eSig (flattenECCAconf A) (flattenECCAconf B)
  | Pair v1 v2 A => ePair (flattenECCAval v1) (flattenECCAval v2) (flattenECCAconf A)
  | Tru => eTru
  | Fls => eFls
  | Bool => eBool
end
with flattenECCAcomp {V: nat}  (e: @ECCAcomp V): @ECCAexp V:=
match e with
  | App v1 v2 => eApp (flattenECCAval v1) (flattenECCAval v2)
  | Val v => flattenECCAval v
  | Fst v => eFst (flattenECCAval v)
  | Snd v => eSnd (flattenECCAval v)
(*   | Subst x arg body => eSubst (flattenECCAval x) (flattenECCAval arg) (flattenECCAval body) *)
end
with flattenECCAconf {V: nat}  (e: @ECCAconf V): @ECCAexp V:=
match e with
  | Comp e => flattenECCAcomp e
  | Let A B => eLet (flattenECCAcomp A) (flattenECCAconf B)
  | If v m1 m2 => eIf (flattenECCAval v) (flattenECCAconf m1) (flattenECCAconf m2)
end.

Fixpoint getECCAconf {V: nat} (e: @ECCAexp V) : option (@ECCAconf V) :=
match e with
  | eLet A B => 
      match (getECCAconf A) with
        | Some (Comp A) => match (getECCAconf B) with
          | Some B => Some (Let A B)
          | None => None
          end
        | _ => None
        end
  | eIf v m1 m2 =>
      let m1 := (getECCAconf m1) in
      let m2 := (getECCAconf m2) in
      let v  := (getECCAconf v) in
      match m1 with
        | Some m1 => match m2 with
          | Some m2 => match v with 
            | Some (Comp (Val v)) => Some (If v m1 m2)
            | _ => None
            end
          | _ => None
          end
        | _ => None
        end 
(* Computations are also configurations *)
  (* should be just this but gah gah gah cannot guess decreasing argument of fix:
    | _ => match (getECCAcomp e) with
    | Some m => Some (Comp m)
    | None => None
    end *)
  | eApp v1 v2 =>
      match (getECCAconf v1) with
        | Some (Comp (Val v1)) => match (getECCAconf v2) with
          | Some (Comp (Val v2)) => Some (Comp (App v1 v2))
          | _ => None
          end
        | _ => None
        end
  | eFst v =>
      match (getECCAconf v) with
        | Some (Comp (Val v)) => Some (Comp (Fst v))
        | _ => None
        end
  | eSnd v =>
      match (getECCAconf v) with
        | Some (Comp (Val v)) => Some (Comp (Snd v))
        | _ => None
        end
(*   | eSubst x arg body =>
      let x := (getECCAval x) in
      let arg := (getECCAval arg) in
      let body  := (getECCAval body) in
      match x with
        | Some x => match arg with
          | Some arg => match body with 
            | Some body => Some (Comp (Subst x arg body))
            | None => None
            end
          | None => None
          end
        | None => None
        end   *)
(* Values are also computations which are also configurations *)
  | eId x => Some (Comp (Val (Id x)))
  | eUni U => Some (Comp (Val (Uni U)))
  | ePi A B =>
      match (getECCAconf A) with
        | Some A => match (getECCAconf B) with
          | Some B => Some (Comp (Val (Pi A B)))
          | None => None
          end
        | None => None
        end
  | eAbs A B =>
      match (getECCAconf A) with
        | Some A => match (getECCAconf B) with
          | Some B => Some (Comp (Val (Abs A B)))
          | None => None
          end
        | None => None
        end
  | eSig A B =>
      match (getECCAconf A) with
        | Some A => match (getECCAconf B) with
          | Some B => Some (Comp (Val (Sig A B)))
          | None => None
          end
        | None => None
        end
  | ePair v1 v2 A => 
      match (getECCAconf v1) with
        | Some (Comp (Val v1)) => match (getECCAconf v2) with
          | Some (Comp (Val v2)) => match (getECCAconf A) with 
            | Some A => Some (Comp (Val (Pair v1 v2 A)))
            | None => None
            end
          | _ => None
          end
        | _ => None
        end
  | eTru => (Some (Comp (Val Tru)))
  | eFls => (Some (Comp (Val Fls)))
  | eBool => (Some (Comp (Val Bool)))
end.

Definition getECCAcomp {V: nat} (e: @ECCAexp V) : option (@ECCAcomp V):=
match (getECCAconf e) with
  | Some (Comp e) => Some e
  | _ => None
end.

Definition getECCAval {V: nat} (e: @ECCAexp V) : option (@ECCAval V):=
match (getECCAconf e) with
  | Some (Comp (Val e)) => Some e
  | _ => None
end.

Definition isANF {V: nat} (e: @ECCAexp V): Prop :=
  exists a, (getECCAconf e) = Some a.
Definition isComp {V: nat} ( e: @ECCAexp V): Prop :=
  exists a, (getECCAcomp e) = Some a.
Definition isVal {V: nat} ( e: @ECCAexp V): Prop :=
  exists a, (getECCAval e) = Some a.

(* Definition reify_Prop_val {V: nat} (e: @ECCAexp V | (@isVal V e)) : @ECCAval V.
Proof. auto.
Qed.
 *)

(* 
Definition open_val {V: nat} (v: @ECCAval (S V)) : @ECCAval V :=
open 

Definition reflect_Prop_val ( e : ECCAexp) : Option (isVal e). *) 

Coercion Val: ECCAval >-> ECCAcomp. 
Coercion Comp: ECCAcomp >-> ECCAconf. 

(* 
=====================================
=======--Type Environments --========
=====================================
*)

Inductive ctxmem:=
| Assum (A: @ECCAexp 0)
| Def (e: @ECCAexp 0) (A: @ECCAexp 0)
| Eq (e1: @ECCAexp 0) (e2: @ECCAexp 0) 
.

Definition ECCAenv:= @context (@ctxmem).

Inductive assumes (g: ECCAenv) (x: atom) (A: ECCAexp) :=
| ass :
  (has g x (Assum A)) ->
  assumes g x A
| def (e: @ECCAexp 0):
  (has g x (Def e A)) ->
  assumes g x A
.


(* (*Defining "g,g'|-"
  Append environment g to environment g'*)
Fixpoint appendEnv (g g': ECCAenv) :=
match g' with
| Empty => g
| Assum g'' x A => Assum (appendEnv g g'') x A
| Def g'' x A => Def (appendEnv g g'') x A
| Eq g'' x A => Eq (appendEnv g g'') x A
end. *)

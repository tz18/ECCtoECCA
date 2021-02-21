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

Inductive val {V: nat}: Type :=
  | Id (x: @atom V)
  | Uni (U: universe)
  | Pi (A: conf) (B: @conf (S V))
  | Abs (A: conf) (B: @conf (S V))
  | Sig (A: conf) (B: @conf (S V))
  | Pair (v1 v2: val) (A: @conf V)
  | Tru
  | Fls
  | Bool
with
conf {V: nat}: Type :=
  | Comp (e: comp)
  | Let (A: comp) (B: @conf (S V))
  | If (v: val) (m1 m2: conf)
with
comp {V: nat}: Type :=
  | App (v1 v2: val)
  | Val (v: val)
  | Fst (v: val)
  | Snd (v: val)
.

(* Mutual induction Scheme *)
Scheme val_conf_mut := Induction for val Sort Prop
with conf_comp_mut := Induction for conf Sort Prop
with comp_val_mut := Induction for comp Sort Prop.

Combined Scheme val_conf_comp_comb from val_conf_mut, conf_comp_mut, comp_val_mut.

(* Fixpoint open_val a {V} (t: @val (S V)):=
match t with 
  | Id x => Id (openv a v)
  | Pair v1 v2 A => Pair (open_val a v1) (open_val a v2) (open_conf a A)
  | Pi A B(A: conf) (B: @conf (S V)) => Pi (open_conf a A) (open_conf a B)
  | Abs A B(A: conf) (B: @conf (S V)) => Abs (open_conf a A) (open_conf a B)
  | Sig A B(A: conf) (B: @conf (S V)) => Sig (open_conf a A) (open_conf a B)
  | (Uni U) as v | Tru as v | Fls as v | Bool as v => v
end
with 
open_comp a {V} (t: @comp (S V)) :=
match
  | App v1 v2 => App (open_val a v1) (open_val a v2)
  | Val v => Val (open_val a v)
  | Fst v => Fst (open_val a v)
  | Snd v => Snd (open_val a v)
end
open_conf a {V} (t: @conf (S V)) :=
match
  | Comp e => Comp (open_comp a e)
  | Let A B => Let (open_comp a A) (open_comp a B)
end *)


Hint Constructors val. 
Coercion Id: atom >-> val.
Bind Scope ECCA_scope with val.
Bind Scope ECCA_scope with conf.
Bind Scope ECCA_scope with comp.


Inductive exp {V: nat}: Type :=
  | eId (x: @atom V)
  | eUni (U: universe)
  | ePi (A: exp) (B: @exp (S V))
  | eAbs (A: exp) (B: @exp (S V))
  | eSig (A: exp) (B: @exp (S V))
  | ePair (v1 v2: exp) (A: exp)
  | eTru
  | eFls
  | eBool
  | eLet (A: exp) (B: @exp (S V))
  | eIf (v: exp) (e1 e2: exp) 
  | eApp (v1 v2: exp)
  | eFst (v: exp)
  | eSnd (v: exp)
(*   | eSubst (x arg body: exp) *)
.

(* Approach: If we have an exp with a proof
 that we can get an conf out of it, we should be able to
 extract the conf. Three fundamental naming operations cannot break ANF:
 wk, open, and close. The only operation that could potentially break ANF is bind.
 Let's apply these constructors by operating over the exp,
 preserving the proof that it is ANF,
 and extracting the conf back after.*)

Hint Constructors exp.

Module ECCATerm <: Term.
  Definition term := @exp.
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

Fixpoint unrestrict_val {V: nat} (v: @val V): @exp V :=
match v with
  | Id x => eId x
  | Uni U => eUni U
  | Pi A B => ePi (unrestrict_conf A) (unrestrict_conf B) 
  | Abs A B => eAbs (unrestrict_conf A) (unrestrict_conf B)
  | Sig A B => eSig (unrestrict_conf A) (unrestrict_conf B)
  | Pair v1 v2 A => ePair (unrestrict_val v1) (unrestrict_val v2) (unrestrict_conf A)
  | Tru => eTru
  | Fls => eFls
  | Bool => eBool
end
with unrestrict_comp {V: nat}  (e: @comp V): @exp V:=
match e with
  | App v1 v2 => eApp (unrestrict_val v1) (unrestrict_val v2)
  | Val v => unrestrict_val v
  | Fst v => eFst (unrestrict_val v)
  | Snd v => eSnd (unrestrict_val v)
(*   | Subst x arg body => eSubst (unrestrict_val x) (unrestrict_val arg) (unrestrict_val body) *)
end
with unrestrict_conf {V: nat}  (e: @conf V): @exp V:=
match e with
  | Comp e => unrestrict_comp e
  | Let A B => eLet (unrestrict_comp A) (unrestrict_conf B)
  | If v m1 m2 => eIf (unrestrict_val v) (unrestrict_conf m1) (unrestrict_conf m2)
end.

Fixpoint restrict_conf {V: nat} (e: @exp V) : option (@conf V) :=
match e with
  | eLet A B => 
      match (restrict_conf A) with
        | Some (Comp A) => match (restrict_conf B) with
          | Some B => Some (Let A B)
          | None => None
          end
        | _ => None
        end
  | eIf v m1 m2 =>
      let m1 := (restrict_conf m1) in
      let m2 := (restrict_conf m2) in
      let v  := (restrict_conf v) in
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
    | _ => match (restrict_comp e) with
    | Some m => Some (Comp m)
    | None => None
    end *)
  | eApp v1 v2 =>
      match (restrict_conf v1) with
        | Some (Comp (Val v1)) => match (restrict_conf v2) with
          | Some (Comp (Val v2)) => Some (Comp (App v1 v2))
          | _ => None
          end
        | _ => None
        end
  | eFst v =>
      match (restrict_conf v) with
        | Some (Comp (Val v)) => Some (Comp (Fst v))
        | _ => None
        end
  | eSnd v =>
      match (restrict_conf v) with
        | Some (Comp (Val v)) => Some (Comp (Snd v))
        | _ => None
        end
(*   | eSubst x arg body =>
      let x := (restrict_val x) in
      let arg := (restrict_val arg) in
      let body  := (restrict_val body) in
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
      match (restrict_conf A) with
        | Some A => match (restrict_conf B) with
          | Some B => Some (Comp (Val (Pi A B)))
          | None => None
          end
        | None => None
        end
  | eAbs A B =>
      match (restrict_conf A) with
        | Some A => match (restrict_conf B) with
          | Some B => Some (Comp (Val (Abs A B)))
          | None => None
          end
        | None => None
        end
  | eSig A B =>
      match (restrict_conf A) with
        | Some A => match (restrict_conf B) with
          | Some B => Some (Comp (Val (Sig A B)))
          | None => None
          end
        | None => None
        end
  | ePair v1 v2 A => 
      match (restrict_conf v1) with
        | Some (Comp (Val v1)) => match (restrict_conf v2) with
          | Some (Comp (Val v2)) => match (restrict_conf A) with 
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

Definition restrict_comp {V: nat} (e: @exp V) : option (@comp V):=
match (restrict_conf e) with
  | Some (Comp e) => Some e
  | _ => None
end.

Definition restrict_val {V: nat} (e: @exp V) : option (@val V):=
match (restrict_conf e) with
  | Some (Comp (Val e)) => Some e
  | _ => None
end.

Definition isConf {V: nat} (e: @exp V): Prop :=
  exists a, (restrict_conf e) = Some a.
Definition isComp {V: nat} ( e: @exp V): Prop :=
  exists a, (restrict_comp e) = Some a.
Definition isVal {V: nat} ( e: @exp V): Prop :=
  exists a, (restrict_val e) = Some a.

(* Definition reify_Prop_val {V: nat} (e: @exp V | (@isVal V e)) : @val V.
Proof. auto.
Qed.
 *)

(* 
Definition open_val {V: nat} (v: @val (S V)) : @val V :=
open 

Definition reflect_Prop_val ( e : exp) : Option (isVal e). *) 

Coercion Val: val >-> comp. 
Coercion Comp: comp >-> conf. 
(*
=====================================
=============--Size--================
=====================================
*)

Fixpoint esize {V: nat} (e: @exp V) : nat :=
  match e with
  | eId _ => 1
  | eUni _ => 1
  | ePi A B => 1 + (esize A) + (esize B)
  | eAbs A e => 1 + (esize A) + (esize e)
  | eApp e1 e2 => 1 + (esize e1) + (esize e2)
  | eLet e1 e2 => 1 + (esize e1) + (esize e2)
  | eSig A B => 1 + (esize A) + (esize B)
  | ePair e1 e2 A => 1 + (esize e1) + (esize e2) + (esize A)
  | eFst e => 1 + (esize e)
  | eSnd e => 1 + (esize e)
  | eIf e e1 e2 => 1 + (esize e) + (esize e1) + (esize e2) 
  | eTru => 1
  | eFls => 1
  | eBool => 1
end.

(* 
=====================================
=======--Type Environments--=========
=====================================
*)

Inductive ctxmem :=
| Assum (A: @exp 0)
| Def (e: @exp 0) (A: @exp 0)
| Eq (e1: @exp 0) (e2: @exp 0) 
.

Definition env := @context ctxmem.

Inductive assumes (g: env) (x: atom) (A: exp) :=
| ass :
  (has g x (Assum A)) ->
  assumes g x A
| def (e: @exp 0):
  (has g x (Def e A)) ->
  assumes g x A
.

Hint Constructors assumes.

Lemma ctx_has (g: env) (x: name) (a: ctxmem):
  (has (ctx_cons g x a) (free x) a).
Proof.
  unfold has. rewrite rw_closev_same. unfold bindv. auto.
Qed.


(* Defining "g,g'|-"
  Append environment g to environment g'*)
Fixpoint append (g g': env) :=
match g with
| ctx_empty => g'
| g'' & x ~ A => ((append g'' g') & x ~ A)
end. 

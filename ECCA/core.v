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

Fixpoint flattenval {V: nat} (v: @val V): @exp V :=
match v with
  | Id x => eId x
  | Uni U => eUni U
  | Pi A B => ePi (flattenconf A) (flattenconf B) 
  | Abs A B => eAbs (flattenconf A) (flattenconf B)
  | Sig A B => eSig (flattenconf A) (flattenconf B)
  | Pair v1 v2 A => ePair (flattenval v1) (flattenval v2) (flattenconf A)
  | Tru => eTru
  | Fls => eFls
  | Bool => eBool
end
with flattencomp {V: nat}  (e: @comp V): @exp V:=
match e with
  | App v1 v2 => eApp (flattenval v1) (flattenval v2)
  | Val v => flattenval v
  | Fst v => eFst (flattenval v)
  | Snd v => eSnd (flattenval v)
(*   | Subst x arg body => eSubst (flattenval x) (flattenval arg) (flattenval body) *)
end
with flattenconf {V: nat}  (e: @conf V): @exp V:=
match e with
  | Comp e => flattencomp e
  | Let A B => eLet (flattencomp A) (flattenconf B)
  | If v m1 m2 => eIf (flattenval v) (flattenconf m1) (flattenconf m2)
end.

Fixpoint getconf {V: nat} (e: @exp V) : option (@conf V) :=
match e with
  | eLet A B => 
      match (getconf A) with
        | Some (Comp A) => match (getconf B) with
          | Some B => Some (Let A B)
          | None => None
          end
        | _ => None
        end
  | eIf v m1 m2 =>
      let m1 := (getconf m1) in
      let m2 := (getconf m2) in
      let v  := (getconf v) in
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
    | _ => match (getcomp e) with
    | Some m => Some (Comp m)
    | None => None
    end *)
  | eApp v1 v2 =>
      match (getconf v1) with
        | Some (Comp (Val v1)) => match (getconf v2) with
          | Some (Comp (Val v2)) => Some (Comp (App v1 v2))
          | _ => None
          end
        | _ => None
        end
  | eFst v =>
      match (getconf v) with
        | Some (Comp (Val v)) => Some (Comp (Fst v))
        | _ => None
        end
  | eSnd v =>
      match (getconf v) with
        | Some (Comp (Val v)) => Some (Comp (Snd v))
        | _ => None
        end
(*   | eSubst x arg body =>
      let x := (getval x) in
      let arg := (getval arg) in
      let body  := (getval body) in
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
      match (getconf A) with
        | Some A => match (getconf B) with
          | Some B => Some (Comp (Val (Pi A B)))
          | None => None
          end
        | None => None
        end
  | eAbs A B =>
      match (getconf A) with
        | Some A => match (getconf B) with
          | Some B => Some (Comp (Val (Abs A B)))
          | None => None
          end
        | None => None
        end
  | eSig A B =>
      match (getconf A) with
        | Some A => match (getconf B) with
          | Some B => Some (Comp (Val (Sig A B)))
          | None => None
          end
        | None => None
        end
  | ePair v1 v2 A => 
      match (getconf v1) with
        | Some (Comp (Val v1)) => match (getconf v2) with
          | Some (Comp (Val v2)) => match (getconf A) with 
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

Definition getcomp {V: nat} (e: @exp V) : option (@comp V):=
match (getconf e) with
  | Some (Comp e) => Some e
  | _ => None
end.

Definition getval {V: nat} (e: @exp V) : option (@val V):=
match (getconf e) with
  | Some (Comp (Val e)) => Some e
  | _ => None
end.

Definition isConf {V: nat} (e: @exp V): Prop :=
  exists a, (getconf e) = Some a.
Definition isComp {V: nat} ( e: @exp V): Prop :=
  exists a, (getcomp e) = Some a.
Definition isVal {V: nat} ( e: @exp V): Prop :=
  exists a, (getval e) = Some a.

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
=======--Type Environments --========
=====================================
*)

Inductive ctxmem {V: nat} :=
| Assum (A: @exp V)
| Def (e: @exp V) (A: @exp V)
| Eq (e1: @exp V) (e2: @exp V) 
.

Definition env {V: nat} := @context (@ctxmem V).

Inductive assumes {V: nat} (g: env) (x: atom) (A: @exp V) :=
| ass :
  (has g x (Assum A)) ->
  assumes g x A
| def (e: @exp V):
  (has g x (Def e A)) ->
  assumes g x A
.

Lemma ctx_has {V: nat} (g: @env V) (x: name) (a: ctxmem):
  (has (ctx_cons g x a) (free x) a).
Proof.
  unfold has. rewrite rw_closev_same. unfold bindv. auto.
Qed.


(* Defining "g,g'|-"
  Append environment g to environment g'*)
Fixpoint append {V:nat} (g g': @env V) :=
match g with
| ctx_empty => g'
| g'' & x ~ A => ((append g'' g') & x ~ A)
end. 

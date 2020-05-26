Require Export Atom.

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
  | Pi (A: @ECCAconf V) (B: @ECCAconf (S V))
  | Abs (A: @ECCAconf V) (B: @ECCAconf (S V))
  | Sig (A: @ECCAconf V) (B: @ECCAconf (S V))
  | Pair (v1 v2: ECCAval) (A: @ECCAconf V)
  | Tru
  | Fls
  | Bool
with
ECCAconf {V: nat}: Type :=
  | Comp (e: @ECCAcomp V)
  | Let (A: @ECCAcomp V) (B: @ECCAconf (S V))
(*   | If (v: ECCAval) (m1 m2: ECCAconf) *)
with
ECCAcomp {V: nat}: Type :=
  | App (v1 v2: @ECCAval V)
  | Val (v: @ECCAval V)
  | Fst (v: @ECCAval V)
  | Snd (v: @ECCAval V)
(*   | Subst (x arg body: ECCAval) *)
.

Hint Constructors ECCAval. 
Coercion Id: atom >-> ECCAval.
Bind Scope ECCA_scope with ECCAval.
Bind Scope ECCA_scope with ECCAconf.
Bind Scope ECCA_scope with ECCAcomp.


Inductive ECCAexp {V: nat}: Type :=
  | eId (x: @atom V)
  | eUni (U: ECCuni)
  | ePi (A: @ECCAexp V) (B: @ECCAexp (S V))
  | eAbs (A: @ECCAexp V) (B: @ECCAexp (S V))
  | eSig (A: @ECCAexp V) (B: @ECCAexp (S V))
  | ePair (v1 v2: @ECCAexp V) (A: ECCAexp)
  | eTru
  | eFls
  | eBool
  | eLet (A: @ECCAexp V) (B: @ECCAexp (S V))
(*   | eIf (v: ECCAexp) (m1 m2: ECCAexp) *)
  | eApp (v1 v2: @ECCAexp V)
  | eFst (v: @ECCAexp V)
  | eSnd (v: @ECCAexp V)
(*   | eSubst (x arg body: ECCAexp) *)
.

Hint Constructors ECCAexp.


(* 
============================================================
=======--Moving from restricted to unrestricted--=========== 
============================================================
*)

Fixpoint flattenECCAval (e: ECCAval) {V: nat}: ECCAexp :=
match e with
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
with flattenECCAcomp (e: ECCAcomp): ECCAexp :=
match e with
  | App v1 v2 => eApp (flattenECCAval v1) (flattenECCAval v2)
  | Val v => flattenECCAval v
  | Fst v => eFst (flattenECCAval v)
  | Snd v => eSnd (flattenECCAval v)
(*   | Subst x arg body => eSubst (flattenECCAval x) (flattenECCAval arg) (flattenECCAval body) *)
end
with flattenECCAconf (e: ECCAconf): ECCAexp :=
match e with
  | Comp e => flattenECCAcomp e
  | Let A B => eLet (flattenECCAcomp A) (flattenECCAconf B)
(*   | If v m1 m2 => eIf (flattenECCAval v) (flattenECCAconf m1) (flattenECCAconf m2) *)
end.

Fixpoint getECCAval (e: ECCAexp): option ECCAval :=
match e with
  | eId x => Some (Id x)
  | eUni U => Some (Uni U)
  | ePi x A B => 
      let A := (getECCAconf A) in
      let B := (getECCAconf B) in
      match A with
        | Some A => match B with
          | Some B => Some (Pi x A B)
          | None => None
          end
        | None => None
        end
  | eAbs x A B =>
      let A := (getECCAconf A) in
      let B := (getECCAconf B) in
      match A with
        | Some A => match B with
          | Some B => Some (Abs x A B)
          | None => None
          end
        | None => None
        end
  | eSig x A B =>
      let A := (getECCAconf A) in
      let B := (getECCAconf B) in
      match A with
        | Some A => match B with
          | Some B => Some (Sig x A B)
          | None => None
          end
        | None => None
        end
  | ePair v1 v2 A => 
      let v1 := (getECCAval v1) in
      let v2 := (getECCAval v2) in
      let A  := (getECCAconf A) in
      match v1 with
        | Some v1 => match v2 with
          | Some v2 => match A with 
            | Some A => Some (Pair v1 v2 A)
            | None => None
            end
          | None => None
          end
        | None => None
        end
  | eTru => (Some Tru)
  | eFls => (Some Fls)
  | eBool => (Some Bool)
  | _ => None
end
with getECCAconf (e: ECCAexp): option ECCAconf :=
match e with
  | eLet x A B => 
      let A := (getECCAcomp A) in
      let B := (getECCAconf B) in
      match A with
        | Some A => match B with
          | Some B => Some (Let x A B)
          | None => None
          end
        | None => None
        end
(*   | eIf v m1 m2 =>
      let m1 := (getECCAconf m1) in
      let m2 := (getECCAconf m2) in
      let v  := (getECCAval v) in
      match m1 with
        | Some m1 => match m2 with
          | Some m2 => match v with 
            | Some v => Some (If v m1 m2)
            | None => None
            end
          | None => None
          end
        | None => None
        end *)
(* Computations are also configurations *)
  | eApp v1 v2 =>
      let v1 := (getECCAval v1) in
      let v2 := (getECCAval v2) in
      match v1 with
        | Some v1 => match v2 with
          | Some v2 => Some (Comp (App v1 v2))
          | None => None
          end
        | None => None
        end
  | eFst v =>
      let v := (getECCAval v) in
      match v with
        | Some v => Some (Comp (Fst v))
        | None => None
        end
  | eSnd v =>
      let v := (getECCAval v) in
      match v with
        | Some v => Some (Comp (Snd v))
        | None => None
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
  | ePi x A B => 
      let A := (getECCAconf A) in
      let B := (getECCAconf B) in
      match A with
        | Some A => match B with
          | Some B => Some (Comp (Val (Pi x A B)))
          | None => None
          end
        | None => None
        end
  | eAbs x A B =>
      let A := (getECCAconf A) in
      let B := (getECCAconf B) in
      match A with
        | Some A => match B with
          | Some B => Some (Comp (Val (Abs x A B)))
          | None => None
          end
        | None => None
        end
  | eSig x A B =>
      let A := (getECCAconf A) in
      let B := (getECCAconf B) in
      match A with
        | Some A => match B with
          | Some B => Some (Comp (Val (Sig x A B)))
          | None => None
          end
        | None => None
        end
  | ePair v1 v2 A => 
      let v1 := (getECCAval v1) in
      let v2 := (getECCAval v2) in
      let A  := (getECCAconf A) in
      match v1 with
        | Some v1 => match v2 with
          | Some v2 => match A with 
            | Some A => Some (Comp (Val (Pair v1 v2 A)))
            | None => None
            end
          | None => None
          end
        | None => None
        end
  | eTru => (Some (Comp (Val Tru)))
  | eFls => (Some (Comp (Val Fls)))
  | eBool => (Some (Comp (Val Bool)))
end
with getECCAcomp (e: ECCAexp): option ECCAcomp :=
match e with
  | eApp v1 v2 =>
      let v1 := (getECCAval v1) in
      let v2 := (getECCAval v2) in
      match v1 with
        | Some v1 => match v2 with
          | Some v2 => Some (App v1 v2)
          | None => None
          end
        | None => None
        end
  | eFst v =>
      let v := (getECCAval v) in
      match v with
        | Some v => Some (Fst v)
        | None => None
        end
  | eSnd v =>
      let v := (getECCAval v) in
      match v with
        | Some v => Some (Snd v)
        | None => None
        end
(*   | eSubst x arg body =>
      let x := (getECCAval x) in
      let arg := (getECCAval arg) in
      let body  := (getECCAval body) in
      match x with
        | Some x => match arg with
          | Some arg => match body with 
            | Some body => Some (Subst x arg body)
            | None => None
            end
          | None => None
          end
        | None => None
        end   *)
(* Values are also computations *)
  | eId x => Some (Val (Id x))
  | eUni U => Some (Val (Uni U))
  | ePi x A B => 
      let A := (getECCAconf A) in
      let B := (getECCAconf B) in
      match A with
        | Some A => match B with
          | Some B => Some (Val (Pi x A B))
          | None => None
          end
        | None => None
        end
  | eAbs x A B =>
      let A := (getECCAconf A) in
      let B := (getECCAconf B) in
      match A with
        | Some A => match B with
          | Some B => Some (Val (Abs x A B))
          | None => None
          end
        | None => None
        end
  | eSig x A B =>
      let A := (getECCAconf A) in
      let B := (getECCAconf B) in
      match A with
        | Some A => match B with
          | Some B => Some (Val (Sig x A B))
          | None => None
          end
        | None => None
        end
  | ePair v1 v2 A => 
      let v1 := (getECCAval v1) in
      let v2 := (getECCAval v2) in
      let A  := (getECCAconf A) in
      match v1 with
        | Some v1 => match v2 with
          | Some v2 => match A with 
            | Some A => Some (Val (Pair v1 v2 A))
            | None => None
            end
          | None => None
          end
        | None => None
        end
  | eTru => (Some (Val Tru))
  | eFls => (Some (Val Fls))
  | eBool => (Some (Val Bool))
  | _ => None
end
.

Definition isANF (e: ECCAexp): Prop :=
  exists a, (getECCAconf e) = Some a.
Definition isComp ( e: ECCAexp): Prop :=
  exists a, (getECCAcomp e) = Some a.
Definition isVal ( e: ECCAexp): Prop :=
  exists a, (getECCAval e) = Some a.
(* 
Definition reify_Prop_val { e : ECCAexp} (p : (isVal e)) : ECCAval.
Definition reflect_Prop_val ( e : ECCAexp) : Option (isVal e). *)

Coercion Val: ECCAval >-> ECCAcomp. 
Coercion Comp: ECCAcomp >-> ECCAconf. 

(* 
=====================================
=======--Type Environments --========
=====================================
*)

Inductive ECCAenv: Type :=
  | Empty
  | Assum (g: ECCAenv) (x: atom) (A: ECCAexp)
  | Def (g: ECCAenv) (x: atom) (v: ECCAexp)
  | Eq (g: ECCAenv) (v1 v2: ECCAexp)
.
Hint Constructors ECCAenv. 
Notation "g ',' x '=' e" := (Def g x e) (at level 50, x at level 50): ECCA_scope.
Notation "g ',' x ':' e" := (Assum g x e) (at level 50, x at level 50): ECCA_scope.

Inductive ECCA_LookupTypeR : ECCAenv -> atom -> ECCAexp -> Prop:=
  | aLT_gFirst (g': ECCAenv) (x: atom) (A: ECCAexp):
      ECCA_LookupTypeR (Assum g' x A) x A
  | aLT_AssumRest (g: ECCAenv) (x x': atom) (A a': ECCAexp):
      ECCA_LookupTypeR g x A ->
      (x <> x') ->
      (ECCA_LookupTypeR (Assum g x' a') x A)
  | aLT_DefRest (g: ECCAenv) (x x': atom) (A a': ECCAexp):
      ECCA_LookupTypeR g x A ->
  (*     (x <> x') -> *)
      (ECCA_LookupTypeR (Def g x' a') x A)
  | aLT_EqRest (g: ECCAenv) (x: atom) (v A v': ECCAexp):
      ECCA_LookupTypeR g x A ->
      ECCA_LookupTypeR (Eq g v v') x A 
.
Hint Constructors ECCA_LookupTypeR.


Inductive ECCA_LookupDefR : ECCAenv -> atom -> ECCAexp -> Prop:=
  | aLD_gFirst (g': ECCAenv) (x: atom) (e: ECCAexp) (A: ECCAexp):
      ECCA_LookupDefR (Assum (Def g' x e) x A) x e
  | aLD_AssumRest (g: ECCAenv) (x x': atom) (e: ECCAexp) (a': ECCAexp):
      ECCA_LookupDefR g x e ->
      (x <> x') ->
      (ECCA_LookupDefR (Assum g x' a') x e)
  | aLD_DefRest (g: ECCAenv) (x x': atom) (e e': ECCAexp):
      ECCA_LookupDefR g x e ->
      (x <> x') ->
      (ECCA_LookupDefR (Def g x' e') x e)
  | aLD_EqRest (g: ECCAenv) (x: atom) (v v': ECCAexp) (e: ECCAexp):
      ECCA_LookupDefR g x e ->
      ECCA_LookupDefR (Eq g v v') x e 
.
Hint Constructors ECCA_LookupDefR.


(*should change val to conf *)
Inductive ECCA_LookupEqR : ECCAenv -> ECCAexp -> ECCAexp -> Prop:=
  | aLE_gFirst (g': ECCAenv) (v v': ECCAexp):
    ECCA_LookupEqR (Eq g' v v') v v'
  | aLE_AssumRest (g: ECCAenv) (x : atom) (v v' a: ECCAexp):
      ECCA_LookupEqR g v v' ->
      (ECCA_LookupEqR (Assum g x a) v v')
  | aLE_DefRest (g: ECCAenv) (x: atom) (v v' e: ECCAexp):
      ECCA_LookupEqR g v v' ->
      (ECCA_LookupEqR (Def g x e) v v')
  | aLE_EqRest (g: ECCAenv) (x: atom) (v1 v2 v1' v2': ECCAexp):
      ECCA_LookupEqR g v1 v2 ->
      (v1 <> v1') ->
      ECCA_LookupEqR (Eq g v1' v2') v1 v2 
.
Hint Constructors ECCA_LookupEqR.


(*Defining "g,g'|-"
  Append environment g to environment g'*)
Fixpoint appendEnv (g g': ECCAenv) :=
match g' with
| Empty => g
| Assum g'' x A => Assum (appendEnv g g'') x A
| Def g'' x A => Def (appendEnv g g'') x A
| Eq g'' x A => Eq (appendEnv g g'') x A
end.

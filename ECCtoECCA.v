From Coq Require Import Strings.String.

(* Module ECC. *)

Inductive ECCuni: Type :=
  | uProp
  | uType (i: nat)
.

Inductive ECCexp: Type :=
  | eId (x: string)
  | eUni (U: ECCuni)
  | ePi (x: string) (A B: ECCexp)
  | eAbs (x: string) (A B: ECCexp)
  | eApp  (e1 e2: ECCexp)
  | eLet (x: string) (e1 e2: ECCexp)
(*
  |ECCSig (x: string) (A B: ECCexp)
  |ECCPair (e1 e2 A B: ECCexp)
  |ECCFst (e: ECCexp)
  |ECCSnd (e: ECCexp)
*)
.

Inductive ECCenv: Type :=
  | gDot
  | gTypeDec (x: string) (A: ECCexp)
  | gAssign (x: string) (e: ECCexp)
.

(* End ECC.

Module ECCA. *)

(*
Inductive ECCAuni : Type :=
  | auProp
  | auType (i: nat)
.*)

Inductive ECCAval: Type :=
  | avId (x: string)
  | avUni (U: ECCuni)
  | avPi (x: string) (A B: ECCAconf)
  | avAbs (x: string) (A B: ECCAconf)
with
ECCAconf: Type :=
  | acfComp (e: ECCAcomp)
  | acfLet (x: string) (A: ECCAcomp) (B: ECCAconf)
with 
ECCAcomp: Type :=
  | acpApp (e1 e2: ECCAval)
  | acpVal (e: ECCAval)
.

Inductive ECCAcont: Type :=
  | actHole
  | actLetHole (x: string) (B: ECCAconf)
.

(* End ECCA. *)
Fixpoint fill_hole (e: ECCAcomp) (K: ECCAcont): ECCAconf :=
  match K with
    | actHole => acfComp e
    | actLetHole x B => acfLet x e B
end.
(* {ns : NameState} *)
Fixpoint trans  (e: ECCexp) (K: ECCAcont) : ECCAconf :=
  match e with
    | eId x => (fill_hole (acpVal (avId x)) K)
    | eUni u => (fill_hole (acpVal (avUni u)) K)
    | ePi x A B => (fill_hole (acpVal (avPi x (trans A actHole) (trans B actHole))) K)
    | eAbs x A B => (fill_hole (acpVal (avAbs x (trans A actHole) (trans B actHole))) K)
    | eApp e1 e2 => 
        (trans e1 (actLetHole "x1" 
            (trans e2 (actLetHole "x2" 
                (fill_hole (acpApp (avId "x1") (avId "x2")) K)))))
    | eLet x e1 e2 => (trans e1 (actLetHole "x" 
                          (trans e2 K)))
end.
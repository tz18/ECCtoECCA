Require Import Atom.
Require Import ECC.
Require Import ECCA.

Fixpoint fill_hole (e: ECCAcomp) (K: ECCAcont): ECCAconf :=
  match K with
    | Hole => Comp e
    | LetHole x B => Let x e B
end.

(* Plan: starter function starts namestate at max of atoms in the ECCexp, so all new atoms are higher than old atoms. *)

(* {ns : NameState} *)

Fixpoint trans  (ns: atom) (e: ECCexp) (K: ECCAcont) : ECCAconf :=
  let X := (S ns) in
  let Y := (S (S ns)) in
  let Z := (S (S (S ns))) in
  match e with
    | ECC.Id x => (fill_hole (Val (Id x)) K)
    | ECC.Pi x A B => (fill_hole (Val (Pi (x) (trans ns A Hole) (trans ns B Hole))) K)
    | ECC.Abs x A e => (fill_hole (Val (Abs x (trans ns A Hole) (trans ns e Hole))) K)
    | ECC.App e1 e2 =>
        (trans X e1 (LetHole X
            (trans Y e2 (LetHole Y
                (fill_hole (App (Id X) (Id Y)) K)))))
    | ECC.Let x e1 e2 => (trans ns e1 (LetHole x
                          (trans (ns) e2 K)))
    | ECC.Sig x A B => (fill_hole (Val (Sig x (trans ns A Hole) (trans ns B Hole))) K)
    | ECC.Pair e1 e2 A => (trans X e1 (LetHole X
            (trans Y e2 (LetHole Y
               (trans Z A (LetHole Z
                (fill_hole (Pair (Id X) (Id Y) (Id Z)) K)))))))
    | ECC.Fst e => (trans X e (LetHole X
                   (fill_hole (Fst (Id X)) K)))
    | ECC.Snd e => (trans X e (LetHole X
                   (fill_hole (Snd X) K)))
    | ECC.Tru => (fill_hole (Val Tru) K)
    | ECC.Fls => (fill_hole (Val Fls) K)
    | ECC.Bool=> (fill_hole (Val Bool) K)
    | ECC.Uni u => (fill_hole (Val (Uni u)) K)
    | ECC.If e e1 e2 => (trans X e (LetHole X 
                        (If (Id X) 
                            (trans Y e1 (LetHole Y (fill_hole (Subst X Tru (Id Y)) K)))
                            (trans Y e1 (LetHole Y (fill_hole (Subst X Fls (Id Y)) K))))))
end.

Definition transStarter (e: ECCexp):=
  trans (fresh (ECC.FV e)) e Hole
.

Compute transStarter (LET X := Y in LET Y := type 1 in X)%ECC.
Compute transStarter (fst (<ECC.Tru , ECC.Fls> as 
                            (Si X : ECC.Bool .. (ECC.If X ECC.Bool (P Y : ECC.Bool -> ECC.Bool))))).
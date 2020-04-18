Require Import Atom.
Require Import ECC.
Require Import ECCA_core ECCA_typing.

(* Plan: starter function starts namestate at max of atoms in the ECCexp, so all new atoms are higher than old atoms. *)

(* {ns : NameState} *)

Inductive ECCAcont: Type :=
  | Hole
  | LetHole (x: atom) (E: ECCAconf)
.

Definition fill_hole_r (e: ECCAcomp) (K: ECCAcont): ECCAconf :=
  match K with
    | Hole => e
    | LetHole x B => Let x e B
end.

Fixpoint trans  (ns: atoms) (e: ECCexp) (K: ECCAcont) : ECCAconf :=
  let (X, _) := (atom_fresh ns) in
  let Xns    := (add X ns) in
  let (Y, _) := (atom_fresh Xns)  in
  let Yns    := (add Y Xns) in
  let (Z, _) := (atom_fresh Yns) in
  let Zns    := (add Z Yns) in
  match e with
    | ECC.Id x => (fill_hole_r (Val (Id x)) K)
    | ECC.Pi x A B => (fill_hole_r (Val (Pi (x) (trans ns A Hole) (trans ns B Hole))) K)
    | ECC.Abs x A e => (fill_hole_r (Val (Abs x (trans ns A Hole) (trans ns e Hole))) K)
    | ECC.App e1 e2 =>
        (trans Xns e1 (LetHole X
            (trans Yns e2 (LetHole Y
                (fill_hole_r (App (Id X) (Id Y)) K)))))
    | ECC.Let x e1 e2 => (trans ns e1 (LetHole x
                          (trans (ns) e2 K)))
    | ECC.Sig x A B => (fill_hole_r (Val (Sig x (trans ns A Hole) (trans ns B Hole))) K)
    | ECC.Pair e1 e2 A => (trans Xns e1 (LetHole X
            (trans Yns e2 (LetHole Y
               (trans Zns A (LetHole Z
                (fill_hole_r (Pair (Id X) (Id Y) (Id Z)) K)))))))
    | ECC.Fst e => (trans Xns e (LetHole X
                   (fill_hole_r (Fst (Id X)) K)))
    | ECC.Snd e => (trans Xns e (LetHole X
                   (fill_hole_r (Snd X) K)))
    | ECC.Tru => (fill_hole_r (Val Tru) K)
    | ECC.Fls => (fill_hole_r (Val Fls) K)
    | ECC.Bool=> (fill_hole_r (Val Bool) K)
    | ECC.Uni u => (fill_hole_r (Val (Uni u)) K)
(*     | ECC.If e e1 e2 => (trans X e (LetHole X 
                        (If (Id X) 
                            (trans Y e1 (LetHole Y (fill_hole (Subst X Tru (Id Y)) K)))
                            (trans Y e1 (LetHole Y (fill_hole (Subst X Fls (Id Y)) K)))))) *)
end.

Definition transStarter (e: ECCexp):=
  trans (ECC.FV e) e Hole
.

Compute transStarter (LET X := Y in LET Y := type 1 in X)%ECC.(* 
Compute transStarter (fst (<ECC.Tru , ECC.Fls> as 
                            (Si X : ECC.Bool .. (ECC.If X ECC.Bool (P Y : ECC.Bool -> ECC.Bool))))). *)
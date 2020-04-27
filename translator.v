Require Import Atom.
Require Import ECC.
Require Import ECCA_core ECCA_typing ECCA_continuations.

Fixpoint transWork  (ns: atoms) (e: ECCexp) (K: cont_r) : ECCAconf :=
  let (X, _) := (atom_fresh ns) in
  let Xns    := (add X ns) in
  let (Y, _) := (atom_fresh Xns)  in
  let Yns    := (add Y Xns) in
  let (Z, _) := (atom_fresh Yns) in
  let Zns    := (add Z Yns) in
  match e with
    | ECC.Id x => (fill_hole_r (Val (Id x)) K)
    | ECC.Pi x A B => (fill_hole_r (Val (Pi (x) (transWork ns A rHole) (transWork ns B rHole))) K)
    | ECC.Abs x A e => (fill_hole_r (Val (Abs x (transWork ns A rHole) (transWork ns e rHole))) K)
    | ECC.App e1 e2 =>
        (transWork Xns e1 (rLetHole X
            (transWork Yns e2 (rLetHole Y
                (fill_hole_r (App (Id X) (Id Y)) K)))))
    | ECC.Let x e1 e2 => (transWork ns e1 (rLetHole x
                          (transWork (ns) e2 K)))
    | ECC.Sig x A B => (fill_hole_r (Val (Sig x (transWork ns A rHole) (transWork ns B rHole))) K)
    | ECC.Pair e1 e2 A => (transWork Xns e1 (rLetHole X
            (transWork Yns e2 (rLetHole Y
               (transWork Zns A (rLetHole Z
                (fill_hole_r (Pair (Id X) (Id Y) (Id Z)) K)))))))
    | ECC.Fst e => (transWork Xns e (rLetHole X
                   (fill_hole_r (Fst (Id X)) K)))
    | ECC.Snd e => (transWork Xns e (rLetHole X
                   (fill_hole_r (Snd X) K)))
    | ECC.Tru => (fill_hole_r (Val Tru) K)
    | ECC.Fls => (fill_hole_r (Val Fls) K)
    | ECC.Bool=> (fill_hole_r (Val Bool) K)
    | ECC.Uni u => (fill_hole_r (Val (Uni u)) K)
(*     | ECC.If e e1 e2 => (transWork X e (rLetHole X 
                        (If (Id X) 
                            (transWork Y e1 (rLetHole Y (fill_hole (Subst X Tru (Id Y)) K)))
                            (transWork Y e1 (rLetHole Y (fill_hole (Subst X Fls (Id Y)) K)))))) *)
end.

Definition trans (e: ECCexp):=
  transWork (ECC.FV e) e rHole
.

Fixpoint transEnv (g: ECCenv):=
match g with
| ECC.Empty => Empty
| ECC.Assum g x A => Assum (transEnv g) x (flattenECCAconf (trans A))
| ECC.Def g x v => Def (transEnv g) x (flattenECCAconf (trans v))
end.

Compute trans (LET X := Y in LET Y := type 1 in X)%ECC.
(* Compute trans (fst (<ECC.Tru , ECC.Fls> as 
                            (Si X : ECC.Bool .. (ECC.If X ECC.Bool (P Y : ECC.Bool -> ECC.Bool))))). *)
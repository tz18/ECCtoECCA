Require Import Atom.
Require Import ECC.
Require Import ECCA_core ECCA_typing ECCA_continuations.
Require Import String.
Parameter wk_conf: forall {V: nat}, @ECCAconf V -> @ECCAconf (S V).
Parameter wk_cont: forall {V: nat}, @cont_r V -> @cont_r (S V).
Parameter close_cont: forall {V: nat}, (name) -> @cont_r (S V) -> @cont_r (V).
(* Parameter close_conf: forall {V: nat}, (name) -> @ECCAconf (S V) -> @ECCAconf (V).
 *)
Parameter unwrap : forall {V : nat}, option (@ECCAconf V) -> @ECCAconf V.
Check close.
Check close "x".
Definition close_conf {V: nat} (x: name) (e: @ECCAconf (V)): @ECCAconf (S V) := (unwrap (getECCAconf (close x (flattenECCAconf e)))).


Notation "! k" := (free k) (at level 10, format "! k").

Open Scope string.

Fixpoint transWork  {V: nat} (e: @ECCexp V) (K: @cont_r V) : @ECCAconf V:=
(*   let (X, _) := (atom_fresh ns) in
  let Xns    := (add X ns) in
  let (Y, _) := (atom_fresh Xns)  in
  let Yns    := (add Y Xns) in
  let (Z, _) := (atom_fresh Yns) in
  let Zns    := (add Z Yns) in *)
  match e with
    | ECC.Id x => (fill_hole_r (Val (Id x)) K)
    | ECC.Pi A B => (fill_hole_r (Val (Pi (transWork A rHole) (transWork B rHole))) K)
    | ECC.Abs A e => (fill_hole_r (Val (Abs (transWork A rHole) (transWork e rHole))) K)
    | ECC.Sig A B => (fill_hole_r (Val (Sig (transWork A rHole) (transWork B rHole))) K)
    | ECC.Tru => (fill_hole_r (Val (Tru)) K)
    | ECC.Fls => (fill_hole_r (Val (Fls)) K)
    | ECC.Bool => (fill_hole_r (Val (Bool)) K)
    | ECC.Uni U => (fill_hole_r (Val (Uni U)) K)
    | ECC.Let e1 e2 => (@transWork V e1 (@rLetHole V
                          (@transWork (S V) e2 (wk_cont K))))
    | ECC.App e1 e2 =>
      (@transWork (V) e1 (rLetHole (close_conf ("X1")
         (@transWork (V) (e2) (rLetHole (close_conf ("X2") 
                (fill_hole_r (App (@Id ((V)) (!"X1"))
                                  (@Id ((V)) (!"X2")))
                              K)))))))
    | ECC.Pair e1 e2 A =>
      (@transWork (V) e1 (rLetHole (close_conf ("X1")
         (@transWork (V) (e2) (rLetHole (close_conf ("X2")
                (fill_hole_r (Pair (@Id ((V)) (!"X1"))
                                   (@Id ((V)) (!"X2"))
                                   (transWork A rHole))
                          K)))))))
    | ECC.Fst e =>
      (@transWork (V) e (rLetHole (close_conf ("X1")
                                              (fill_hole_r (Fst (@Id ((V)) (!"X1"))) K))))
    | ECC.Snd e =>
      (@transWork (V) e (rLetHole (close_conf ("X1")
         (fill_hole_r (Snd (@Id ((V)) (!"X1"))) K))))
    
end
.

Definition example:=
(@ECC.Abs 0 ECC.Tru (ECC.ECCRen.close "x1" (ECC.Id (free "x1")))).

Definition example2:=
(@ECC.Abs 0 ECC.Fls (ECC.ECCRen.close "x1" (ECC.Id (free "x1")))).

(* 
Compute example.

Definition ex2 := @ECC.App 0 example example2.

Compute ex2.
Eval cbn in transWork ex2 rHole.
Goal False.
Proof.
remember (transWork ex2 rHole).
unfold ex2 in Heqe.
cbn in Heqe.
simpl in Heqe.
simpl in Heqe.
unfold close_conf in Heqe.
unfold flattenECCAconf in Heqe.
cbv in Heqe.
assert  (@Let 0 (@Abs 0 (@Tru 0) (Id (@closev "x1" 0 (!"x1"))))
         (@close_conf 0 "X1"
            (@Let 0 (@Abs 0 (@Fls 0) (Id (@closev "x1" 0 (!"x1"))))
               (@close_conf 0 "X2" (@App 0 (Id (!"X1")) (Id (!"X2")))))))
=
(@Let 0 (@Abs 0 (@Tru 0) (Id (@closev "x1" 0 (!"x1"))))
            (@Let 1 (@Abs 0 (@Fls 0) (Id (@closev "x1" 0 (!"x1"))))
               (@App 1 (Id (bound l0)) (Id (bound (lS l0)))))).
 *)
(*

    
(*








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
                            (transWork Y e1 (rLetHole Y (fill_hole (Subst X Fls (Id Y)) K)))))) *) *)
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
                            (Si X : ECC.Bool .. (ECC.If X ECC.Bool (P Y : ECC.Bool -> ECC.Bool))))). *) *)

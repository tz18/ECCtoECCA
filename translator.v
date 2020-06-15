Require Import Atom.
Require Import ECC.
Require Import ECCA_core ECCA_core_lemmas ECCA_typing ECCA_continuations.
Require Import String.

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
    | ECC.If e e1 e2 =>
      (@transWork (V) e (rLetHole (close_conf ("X1")
         (If (@Id ((V)) (!"X1")) (@transWork V e1 K) (@transWork V e2 K)))))
end
.

Definition example:=
(@ECC.Abs 0 ECC.Tru (ECC.ECCRen.close "x1" (ECC.Id (free "x1")))).

Definition example2:=
(@ECC.Abs 0 ECC.Fls (ECC.ECCRen.close "x1" (ECC.Id (free "x1")))).

Compute example.

Definition ex2 := @ECC.App 0 example example2.

Compute ex2.
Compute transWork ex2 rHole.

(*     | ECC.If e e1 e2 => (transWork X e (rLetHole X 
                        (If (Id X) 
                            (transWork Y e1 (rLetHole Y (fill_hole (Subst X Tru (Id Y)) K)))
                            (transWork Y e1 (rLetHole Y (fill_hole (Subst X Fls (Id Y)) K)))))) *) 

Definition trans {V: nat}(e: @ECCexp V):=
  @transWork V e rHole
.
(* 
Fixpoint transEnv (g: ECCenv):=
match g with
| ctxempty => ctxempty
| ECC.Assum g x A => Assum (transEnv g) x (flattenECCAconf (trans A))
| ECC.Def g x v => Def (transEnv g) x (flattenECCAconf (trans v))
end. *)

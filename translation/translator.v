Require Import Atom.
Require Import ECC.
Require Import ECCA.core ECCA.core_lemmas ECCA.typing ECCA.continuations.
Require Import Lia Omega.
Require Import String.

Notation "! k" := (free k) (at level 10, format "! k").

Open Scope string.

(*Require Import Recdef.
Require Import Lia.
Require Import Coq.Program.Wf.*)
Require Import Program.
Program Fixpoint transWork (e: @ECC.exp 0) (K: cont_r) {measure (ECC.size e)}: @conf 0:=
  match e with
    | ECC.Id x => (fill_hole_r (Val (Id x)) K)
    | ECC.Pi A B => (fill_hole_r (Val (Pi (transWork A rHole) (close_conf "PiX" (transWork (ECC.ECCRen.open "PiX" B) rHole)))) K)
    | ECC.Abs A e => (fill_hole_r (Val (Abs (transWork A rHole) (close_conf "AbsX" (transWork (ECC.ECCRen.open "AbsX" e) rHole)))) K)
    | ECC.Sig A B => (fill_hole_r (Val (Sig (transWork A rHole) (close_conf "SigX" (transWork (ECC.ECCRen.open "SigX" B) rHole)))) K)
    | ECC.Tru => (fill_hole_r (Val (Tru)) K)
    | ECC.Fls => (fill_hole_r (Val (Fls)) K)
    | ECC.Bool => (fill_hole_r (Val (Bool)) K)
    | ECC.Uni U => (fill_hole_r (Val (Uni U)) K)
    | ECC.Let e1 e2 => (transWork e1 (rLetHole
                          (close_conf "LetX" (transWork (ECC.ECCRen.open "LetX" e2) K))))
    | ECC.App e1 e2 =>
      (transWork e1 (rLetHole (close_conf ("AppX1")
         (transWork e2 (rLetHole (close_conf ("AppX2") 
                (fill_hole_r (App (Id (!"AppX1"))
                                  (Id (!"AppX2")))
                              K)))))))
    | ECC.Pair e1 e2 A =>
      (transWork e1 (rLetHole (close_conf ("X1")
         (transWork (e2) (rLetHole (close_conf ("X2")
                (fill_hole_r (Pair (Id (!"X1"))
                                   (Id (!"X2"))
                                   (transWork A rHole))
                          K)))))))
    | ECC.Fst e =>
      (transWork e (rLetHole (close_conf ("X1")
         (fill_hole_r (Fst (Id (!"X1"))) K))))
    | ECC.Snd e =>
      (transWork e (rLetHole (close_conf ("X1")
         (fill_hole_r (Snd (Id (!"X1"))) K))))
    | ECC.If e e1 e2 =>
      (transWork e (rLetHole (close_conf ("X1")
         (If (Id (!"X1")) (transWork e1 K) (transWork e2 K)))))
end.
Obligations.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; rewrite size_open_id. cbn. lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; rewrite size_open_id. cbn. lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; rewrite size_open_id. cbn. lia. Defined.
Next Obligation. cbn; rewrite size_open_id. cbn. lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.

Definition example:=
(@ECC.Abs 0 ECC.Tru (ECC.ECCRen.close "x1" (ECC.Id (free "x1")))).

Definition example2:=
(@ECC.Abs 0 ECC.Fls (ECC.ECCRen.close "x1" (ECC.Id (free "x1")))).

Compute example.

Definition ex2 := @ECC.App 0 example example2.

Compute ex2.
Compute transWork ex2 rHole.


(* 
(*  *)
Fixpoint transEnv (g: ECCenv):=
match g with
| ctxempty => ctxempty
| ECC.Assum g x A => Assum (transEnv g) x (flattenECCAconf (trans A))
| ECC.Def g x v => Def (transEnv g) x (flattenECCAconf (trans v))
end. *)

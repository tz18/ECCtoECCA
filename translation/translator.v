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
Program Fixpoint transWork (e: @ECC.exp 0) (K: cont) {measure (ECC.size e)}: @ECCA.core.exp 0:=
  match e with
    | ECC.Id x => (fill_hole (eId x) K)
    | ECC.Pi A B => (fill_hole (ePi (transWork A Hole) (close "PiX" (transWork (ECC.ECCRen.open "PiX" B) Hole))) K)
    | ECC.Abs A e => (fill_hole (eAbs (transWork A Hole) (close "AbsX" (transWork (ECC.ECCRen.open "AbsX" e) Hole))) K)
    | ECC.Sig A B => (fill_hole (eSig (transWork A Hole) (close "SigX" (transWork (ECC.ECCRen.open "SigX" B) Hole))) K)
    | ECC.Tru => (fill_hole (eTru) K)
    | ECC.Fls => (fill_hole (eFls) K)
    | ECC.Bool => (fill_hole (eBool) K)
    | ECC.Uni U => (fill_hole (eUni U) K)
    | ECC.Let e1 e2 => (transWork e1 (LetHole
                          (close "LetX" (transWork (ECC.ECCRen.open "LetX" e2) K))))
    | ECC.App e1 e2 =>
      (transWork e1 (LetHole (close ("AppX1")
         (transWork e2 (LetHole (close ("AppX2") 
                (fill_hole (eApp (eId (!"AppX1"))
                                  (eId (!"AppX2")))
                              K)))))))
    | ECC.Pair e1 e2 A =>
      (transWork e1 (LetHole (close ("X1")
         (transWork (e2) (LetHole (close ("X2")
                (fill_hole (ePair (eId (!"X1"))
                                   (eId (!"X2"))
                                   (transWork A Hole))
                          K)))))))
    | ECC.Fst e =>
      (transWork e (LetHole (close ("X1")
         (fill_hole (eFst (eId (!"X1"))) K))))
    | ECC.Snd e =>
      (transWork e (LetHole (close ("X1")
         (fill_hole (eSnd (eId (!"X1"))) K))))
    | ECC.If e e1 e2 =>
      (transWork e (LetHole (close ("X1")
         (eIf (eId (!"X1")) (transWork e1 K) (transWork e2 K)))))
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
Compute transWork ex2 Hole.


(* 
(*  *)
Fixpoint transEnv (g: ECCenv):=
match g with
| ctxempty => ctxempty
| ECC.Assum g x A => Assum (transEnv g) x (flattenECCAconf (trans A))
| ECC.Def g x v => Def (transEnv g) x (flattenECCAconf (trans v))
end. *)


(*Program Fixpoint transWork (e: @ECC.exp 0) (K: cont) {measure (ECC.size e)}: @ECCA.core.exp 0:=
  match e with
    | ECC.Id x => (fill_hole (Val (Id x)) K)
    | ECC.Pi A B => (fill_hole (Val (Pi (transWork A Hole) (close "PiX" (transWork (ECC.ECCRen.open "PiX" B) Hole)))) K)
    | ECC.Abs A e => (fill_hole (Val (Abs (transWork A Hole) (close "AbsX" (transWork (ECC.ECCRen.open "AbsX" e) Hole)))) K)
    | ECC.Sig A B => (fill_hole (Val (Sig (transWork A Hole) (close "SigX" (transWork (ECC.ECCRen.open "SigX" B) Hole)))) K)
    | ECC.Tru => (fill_hole (Val (Tru)) K)
    | ECC.Fls => (fill_hole (Val (Fls)) K)
    | ECC.Bool => (fill_hole (Val (Bool)) K)
    | ECC.Uni U => (fill_hole (Val (Uni U)) K)
    | ECC.Let e1 e2 => (transWork e1 (LetHole
                          (close "LetX" (transWork (ECC.ECCRen.open "LetX" e2) K))))
    | ECC.App e1 e2 =>
      (transWork e1 (LetHole (close ("AppX1")
         (transWork e2 (LetHole (close ("AppX2") 
                (fill_hole (App (Id (!"AppX1"))
                                  (Id (!"AppX2")))
                              K)))))))
    | ECC.Pair e1 e2 A =>
      (transWork e1 (LetHole (close ("X1")
         (transWork (e2) (LetHole (close ("X2")
                (fill_hole (Pair (Id (!"X1"))
                                   (Id (!"X2"))
                                   (transWork A Hole))
                          K)))))))
    | ECC.Fst e =>
      (transWork e (LetHole (close ("X1")
         (fill_hole (Fst (Id (!"X1"))) K))))
    | ECC.Snd e =>
      (transWork e (LetHole (close ("X1")
         (fill_hole (Snd (Id (!"X1"))) K))))
    | ECC.If e e1 e2 =>
      (transWork e (LetHole (close ("X1")
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
Next Obligation. cbn; lia. Defined.*)
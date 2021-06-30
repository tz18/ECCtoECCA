Require Import Atom.
Require Import ECC.
Require Import ECCA.core ECCA.core_lemmas ECCA.typing ECCA.continuations ECCA.continuations_lemmas.
Require Import Lia Omega.
Require Import String.
From Equations Require Import Equations.

Notation "! k" := (free k) (at level 10, format "! k").

Equations foo : nat -> nat := 
  | 0 => 1
  | S n => S (foo n).

Equations translate (e: @ECC.exp 0) (K: cont): (@ECCA.core.exp 0) by wf (@ECC.size 0 e) :=
translate (ECC.Id x) K := (fill_hole (eId x) K) ;
translate (ECC.Pi A B) K := (fill_hole (ePi (translate A Hole) (close "PiX" (translate (ECC.ECCRen.open "PiX" B) Hole))) K);
translate (ECC.Abs A e) K := (fill_hole (eAbs (translate A Hole) (close "AbsX" (translate (ECC.ECCRen.open "AbsX" e) Hole))) K);
translate (ECC.Sig A B) K := (fill_hole (eSig (translate A Hole) (close "SigX" (translate (ECC.ECCRen.open "SigX" B) Hole))) K);
translate (ECC.Tru) K := (fill_hole (eTru) K);
translate (ECC.Fls) K := (fill_hole (eFls) K);
translate (ECC.Bool) K := (fill_hole (eBool) K);
translate (ECC.Uni U) K := (fill_hole (eUni U) K);
translate (ECC.Let e1 e2) K := (translate e1 (LetHole
                          (close "LetX" (translate (ECC.ECCRen.open "LetX" e2) K))));
translate (ECC.App e1 e2) K :=
      (translate e1 (LetHole (close ("AppX1")
         (translate e2 (LetHole (close ("AppX2") 
                (fill_hole (eApp (eId (!"AppX1"))
                                  (eId (!"AppX2")))
                              K)))))));
translate (ECC.Pair e1 e2 A) K :=
      (translate e1 (LetHole (close ("X1")
         (translate (e2) (LetHole (close ("X2")
                (fill_hole (ePair (eId (!"X1"))
                                   (eId (!"X2"))
                                   (translate A Hole))
                          K)))))));
translate (ECC.Fst e) K :=
      (translate e (LetHole (close ("X1")
         (fill_hole (eFst (eId (!"X1"))) K))));
translate (ECC.Snd e) K :=
      (translate e (LetHole (close ("X1")
         (fill_hole (eSnd (eId (!"X1"))) K))));
translate (ECC.If e e1 e2) K :=
      (translate e (LetHole (close ("X1")
         (eIf (eId (!"X1")) (translate e1 K) (translate e2 K)))))
.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; rewrite size_open_id. cbn. lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; rewrite size_open_id. cbn. lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; rewrite size_open_id. cbn. lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; rewrite size_open_id. cbn. lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.
Next Obligation. cbn; lia. Defined.

Search translate.
Hint Rewrite translate_equation_1.

Lemma translate_makes_ANF (e: @ECC.exp 0) (K: cont):
cont_is_ANF K -> isConf (translate e K).
Proof.
intros. funelim (translate e K).
+ rewrite translate_equation_1; apply fill_hole_comp_preserves_conf; auto.
+ rewrite translate_equation_2; apply fill_hole_comp_preserves_conf; auto.
+ rewrite translate_equation_3; apply fill_hole_comp_preserves_conf; auto; apply ValIs; apply Pi; try apply H; cbn; auto; apply close_ANF_iff; apply H0; cbn; auto.
+ rewrite translate_equation_4; apply fill_hole_comp_preserves_conf; auto; apply ValIs; apply Abs; try apply H; cbn; auto; apply close_ANF_iff; apply H0; cbn; auto.
+ rewrite translate_equation_5. apply H0. cbn. apply close_ANF_iff. apply H. cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf. apply H1. auto.
+ rewrite translate_equation_6. apply H0. cbn. apply close_ANF_iff. apply H. auto.
+ rewrite translate_equation_7. apply fill_hole_comp_preserves_conf; auto; apply ValIs; apply Sig; try apply H; cbn; auto; apply close_ANF_iff; apply H0; cbn; auto.
+ rewrite translate_equation_8. apply H1. cbn. apply close_ANF_iff. apply H0. cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf. auto. apply ValIs. apply Pair; auto. apply H. cbn; auto.
+ rewrite translate_equation_9. apply H. cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf; auto.
+ rewrite translate_equation_10. apply H. cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf; auto.
+ rewrite translate_equation_11. apply H1. cbn. apply If; try apply close_ANF_iff; auto.
+ rewrite translate_equation_12. apply fill_hole_comp_preserves_conf; auto.
+ rewrite translate_equation_13. apply fill_hole_comp_preserves_conf; auto.
+ rewrite translate_equation_14. apply fill_hole_comp_preserves_conf; auto.
Qed.

Definition example:=
(@ECC.Abs 0 ECC.Tru (ECC.ECCRen.close "x1" (ECC.Id (free "x1")))).

Definition example2:=
(@ECC.Abs 0 ECC.Fls (ECC.ECCRen.close "x1" (ECC.Id (free "x1")))).

Compute example.

Definition ex2 := @ECC.App 0 example example2.

Compute ex2.
Compute translate ex2 Hole.

(*  *)
(* Fixpoint transEnv (g: ECCenv):=
match g with
| ctxempty => ctxempty
| ECC.Assum g x A => Assum (transEnv g) x (flattenECCAconf (trans A))
| ECC.Def g x v => Def (transEnv g) x (flattenECCAconf (trans v))
end. *)
 *)

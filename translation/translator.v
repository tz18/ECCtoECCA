Require Import Atom.
Require Import ECC.
Require Import ECCA.core ECCA.core_lemmas ECCA.typing ECCA.continuations ECCA.continuations_lemmas.
Require Import Lia Omega.
Require Import String.
From Equations Require Import Equations.

Notation "! k" := (free k) (at level 10, format "! k").
Open Scope term_scope.
Open Scope string.
Equations translate (e: @ECC.exp 0) (K: cont): (@ECCA.core.exp 0) by wf (@ECC.size 0 e) :=
translate (ECC.Id x) K := (fill_hole (eId x) K) ;
translate (ECC.Pi A B) K := (fill_hole (ePi (translate A Hole) (close "k" (translate (ECC.ECCRen.open "k" B) Hole))) K);
translate (ECC.Abs A e) K := (fill_hole (eAbs (translate A Hole) (close "k" (translate (ECC.ECCRen.open "k" e) Hole))) K);
translate (ECC.Sig A B) K := (fill_hole (eSig (translate A Hole) (close "k" (translate (ECC.ECCRen.open "k" B) Hole))) K);
translate (ECC.Tru) K := (fill_hole (eTru) K);
translate (ECC.Fls) K := (fill_hole (eFls) K);
translate (ECC.Bool) K := (fill_hole (eBool) K);
translate (ECC.Uni U) K := (fill_hole (eUni U) K);
translate (ECC.Let e1 e2) K := (translate e1 (LetHole
                          (close "k" (translate (ECC.ECCRen.open "k" e2) (shift_cont "k" K)))));
translate (ECC.App e1 e2) K :=
      (translate e1 (LetHole (close ("k")
         (translate e2 (LetHole (close ("k") 
                (fill_hole (eApp (open "k" (wk (eId (!"k"))))
                                  (eId (!"k")))
                              (shift_cont "k" (shift_cont "k" K)))))))));
translate (ECC.Pair e1 e2 A) K :=
      (translate e1 (LetHole (close ("k")
         (translate (e2) (LetHole (close ("k")
                (fill_hole (ePair (open "k" (wk (eId (!"k"))))
                                   (eId (!"k"))
                                   (translate A Hole)) (* shift here? *)
                          (shift_cont "k" (shift_cont "k" K)))))))));
translate (ECC.Fst e) K :=
      (translate e (LetHole (close ("k")
         (fill_hole (eFst (eId (!"k"))) (shift_cont "k" K)))));
translate (ECC.Snd e) K :=
      (translate e (LetHole (close ("k")
         (fill_hole (eSnd (eId (!"k"))) (shift_cont "k" K)))));
translate (ECC.If e e1 e2) K :=
      (translate e (LetHole (close ("k")
         (eIf (eId (!"k")) (translate e1 (shift_cont "k" K)) (translate e2 (shift_cont "k" K))))))
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

Lemma translate_makes_ANF (e: @ECC.exp 0) (K: cont):
cont_is_ANF K -> isConf (translate e K).
Proof.
intros. funelim (translate e K).
all: simp translate.
1,2,12,13,14: apply fill_hole_comp_preserves_conf; auto.
1,2,5: apply fill_hole_comp_preserves_conf; auto; apply ValIs; constructor; try apply H; cbn; auto; apply close_ANF_iff; apply H0; cbn; auto.
+ apply H0. cbn. apply close_ANF_iff. apply H. cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf. auto. auto.
+ apply H0. cbn. apply close_ANF_iff. apply H. auto.
+ apply H1. cbn. apply close_ANF_iff. apply H0. cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf. auto. apply ValIs. apply Pair; auto. apply H. cbn; auto.
+ apply H. cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf; auto.
+ apply H. cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf; auto.
+ apply H1. cbn. apply If; try apply close_ANF_iff; auto.
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
Fixpoint translateEnv (g: ECC.env):=
match g with
| ctx_empty => ctx_empty
| ctx_cons g x (ECC.Assum A)  => ctx_cons (translateEnv g) x (ECCA.core.Assum (translate A ([⋅])))
| ctx_cons g x (ECC.Def v A) => ctx_cons (translateEnv g) x (ECCA.core.Def (translate v ([⋅])) (translate A ([⋅])))
end.

Notation "'[[' e ']]'" := (translate e Hole) (at level 60).
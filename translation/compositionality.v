Require Import ECC.
Require Import ECCA.core ECCA.core_lemmas ECCA.typing ECCA.equiv_lemmas ECCA.continuations ECCA.continuations_lemmas.
Require Import translator.
Require Import String.
From Equations Require Import Equations.
Open Scope ECCA_scope.

Lemma compositionality (e : ECC.exp) (K K' : cont) (iK: cont_is_ANF K) (iK': cont_is_ANF K'):
  het_compose K' (translate e K) =
  (translate e (cont_compose K' K)).
Proof.
  intros. funelim (translate e K).
  + simp translate; rewrite cont_compose_fill_het_compose; auto; exact "k".
  + simp translate; rewrite cont_compose_fill_het_compose; auto; exact "k".
  + simp translate; rewrite cont_compose_fill_het_compose; auto; try exact "k"; constructor. constructor. apply translate_makes_ANF. cbn; auto.
    apply close_ANF_iff. apply translate_makes_ANF. cbn; auto.
  + simp translate; rewrite cont_compose_fill_het_compose; auto; try exact "k"; constructor. constructor. apply translate_makes_ANF. cbn; auto.
    apply close_ANF_iff. apply translate_makes_ANF. cbn; auto.
  + simp translate. rewrite H0. names. rewrite H. names. rewrite cont_compose_fill_het_compose. rewrite shift_distributes_cont_compose. rewrite shift_distributes_cont_compose. auto.
     - exact "k".
     - apply App; auto.
     - auto.
     - auto.
     - cbn. apply close_ANF_iff. auto.
     - auto.
     - cbn. apply close_ANF_iff. apply translate_makes_ANF. cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf; auto.
     - auto.
  + simp translate. rewrite H0. names. rewrite H. cbn. rewrite shift_distributes_cont_compose. auto.
    cbn. auto. auto. cbn. apply close_ANF_iff.  apply translate_makes_ANF. auto. auto.
  + simp translate; rewrite cont_compose_fill_het_compose; auto; try exact "k"; constructor. constructor. apply translate_makes_ANF. cbn; auto.
    apply close_ANF_iff. apply translate_makes_ANF. cbn; auto.
  + simp translate. rewrite H1. names. rewrite H0. names. rewrite cont_compose_fill_het_compose. rewrite shift_distributes_cont_compose. rewrite shift_distributes_cont_compose. auto.
     - exact "k".
     - apply ValIs. apply Pair; auto. apply translate_makes_ANF. cbn; auto.
     - auto.
     - auto.
     - cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf. auto. constructor. constructor. auto. auto. apply translate_makes_ANF; cbn; auto.
     - auto.
     - cbn. apply close_ANF_iff. apply translate_makes_ANF. cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf; auto. constructor; constructor; auto. apply translate_makes_ANF. cbn; auto.
     - auto.
  + simp translate. rewrite H. names. rewrite cont_compose_fill_het_compose. rewrite shift_distributes_cont_compose. auto.
    exact "k". apply Fst. auto. auto. auto. cbn. apply close_ANF_iff. auto. auto.
  + simp translate. rewrite H. names. rewrite cont_compose_fill_het_compose. rewrite shift_distributes_cont_compose. auto.
    exact "k". apply Snd. auto. auto. auto. cbn. apply close_ANF_iff. auto. auto.
  + simp translate. rewrite H1. cbn. names. rewrite cont_compose_fill_het_compose. 

  1,3,2,4,7,11,12,13: try (unfold transWork; destruct K; destruct K'; simpl; reflexivity).
  - unfold transWork. fold (@transWork V). fold (@transWork V).
    erewrite IHe1.
    simpl.
    erewrite <- IHe2.
    erewrite <- IHe3.
    assert ((rLetHole (het_compose_r (wk_cont K') (close_conf "X1" (If (Id (!"X1")) (transWork e2 K) (transWork e3 K))))) = (rLetHole (close_conf "X1" (If (Id (!"X1")) (het_compose_r K' (transWork e2 K)) (het_compose_r K' (transWork e3 K)))))).
    * assert ((If (Id (!"X1")) (het_compose_r K' (transWork e2 K)) (het_compose_r K' (transWork e3 K))) = (het_compose_r K' (If (Id (!"X1")) (transWork e2 K) (transWork e3 K)))).
      ** auto.
      ** rewrite H. admit.
    * rewrite H. auto.
  - unfold transWork. fold (@transWork V). fold (@transWork V).
    erewrite IHe1. simpl. erewrite <- IHe2.
  - unfold transWork. fold (@transWork V). fold (@transWork V).
    rewrite (IHe1 (rLetHole (close_conf "X1"
             (transWork e2 (rLetHole (close_conf "X2" (fill_hole_r (App (Id (!"X1")) (Id (!"X2"))) K)))))) K').
    simpl.
    rewrite <-  (IHe2 (rLetHole (close_conf "X2" (fill_hole_r (App (Id (!"X1")) (Id (!"X2"))) K))) (wk_cont K')). simpl.
    rewrite (cont_compose_fill_het_compose K' K (App x x0)).
    reflexivity.
  - fold transWork.
    rewrite (IHe1 ns (rLetHole x (transWork ns e2 K)) K'). simpl.
    rewrite (IHe2 ns K K'). reflexivity.
  - fold transWork.
    rewrite (IHe1 (add x ns)
        (rLetHole x
          (transWork (add x0 (add x ns)) e2
             (rLetHole x0
                (transWork (add x1 (add x0 (add x ns))) e3
                       (rLetHole x1 (fill_hole_r (Pair x x0 x1) K)))))) K'). simpl.
    rewrite (IHe2 (add x0 (add x ns)) (rLetHole x0
                (transWork (add x1 (add x0 (add x ns))) e3
                       (rLetHole x1 (fill_hole_r (Pair x x0 x1) K)))) K'). simpl.
    rewrite (IHe3 (add x1 (add x0 (add x ns)))
                  (rLetHole x1 (fill_hole_r (Pair x x0 x1) K)) K'). simpl.
    rewrite (cont_compose_fill_het_compose K' K (Pair x x0 x1)).
    reflexivity.
  - destruct (atom_fresh ns).
    destruct (atom_fresh (add x ns)).
    destruct (atom_fresh (add x0 (add x ns))).
    fold transWork.
    rewrite (IHe (add x ns) (rLetHole x (fill_hole_r (Fst x) K)) K'). simpl.
    rewrite (cont_compose_fill_het_compose K' K (Fst x)).
    reflexivity.
  - destruct (atom_fresh ns).
    destruct (atom_fresh (add x ns)).
    destruct (atom_fresh (add x0 (add x ns))).
    fold transWork.
    rewrite (IHe (add x ns) (rLetHole x (fill_hole_r (Snd x) K)) K'). simpl.
    rewrite (cont_compose_fill_het_compose K' K (Snd x)).
    reflexivity.
Qed.*)
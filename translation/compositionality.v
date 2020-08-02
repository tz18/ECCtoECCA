Require Import ECC.
Require Import ECCA.core ECCA.core_lemmas ECCA.typing ECCA.equiv_lemmas ECCA.continuations.
Require Import translator.
Require Import String.
Lemma compositionality {V: nat} (e : ECC.exp) (K K' : @cont_r V):
  het_compose_r K' (transWork e K) =
  (transWork e (@cont_compose V K' K)).
Proof. Admitted.
(*   intros. induction e.
  1,3,2,4,7,11,12,13: try (unfold transWork; destruct K; destruct K'; simpl; reflexivity).
  - unfold transWork. fold (@transWork V). fold (@transWork V).
    rewrite (IHe1 (rLetHole (close_conf "X1" (If (Id (!"X1")) (transWork e2 K) (transWork e3 K)))) K').
    simpl. shelve.
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
Qed.
 *)
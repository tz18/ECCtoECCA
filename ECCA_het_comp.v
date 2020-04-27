Require Import ECC.
Require Import ECCA_core ECCA_typing.
Require Import translator.
Require Import ECCA_continuations.

Fixpoint het_compose (K : cont_r) (M : ECCAconf) : ECCAconf :=
  match M with
  | Comp e => fill_hole_r e K
  | Let x N M' => Let x N (het_compose K M')
  end.

Fixpoint cont_compose (K : cont_r) (K' : cont_r) : cont_r :=
  match K' with
  | rHole => K
  | rLetHole x M => rLetHole x (het_compose K M)
  end.

(* I am losing my mind, why tf do I have to define the following *)

Lemma cont_compose_snd_arg_hole (K : cont_r) :
  (cont_compose K rHole) = K.
Proof.
  intros. destruct K; reflexivity.
Qed.

Lemma cont_compose_snd_arg_let (K : cont_r) (x : atom) (M : ECCAconf) :
  (cont_compose K (rLetHole x M)) = rLetHole x (het_compose K M).
Proof.
  intros. destruct K; reflexivity.
Qed.

(* This is a little more understandable *)

Lemma cont_compose_fill_het_compose (K K' : cont_r) (N : ECCAcomp) :
  (het_compose K (fill_hole_r N K')) = (fill_hole_r N (cont_compose K K')).
Proof.
  intros. destruct K'.
  + simpl. rewrite cont_compose_snd_arg_hole. reflexivity.
  + simpl. rewrite cont_compose_snd_arg_let. reflexivity.
Qed. 
                         
Lemma compositionality:
  forall (e : ECCexp) (ns : atoms) (K K' : cont_r),
  het_compose K' (transWork ns e K) =
  (transWork ns e (cont_compose K' K)).
Proof.
  intros e. induction e.
  all: unfold transWork; simpl; intros ns K K'.
  all: destruct (atom_fresh ns);
    (destruct (atom_fresh (add x0 ns)); destruct (atom_fresh (add x1 (add x0 ns)))) 
||   (destruct (atom_fresh (add x ns)); destruct (atom_fresh (add x0 (add x ns)))) .
  all: try (destruct K; destruct K'; simpl; reflexivity) .
  - fold transWork.
    rewrite (IHe1 (add x ns) (rLetHole x (transWork (add x0 (add x ns)) e2
                                               (rLetHole x0 (fill_hole_r (App x x0) K)))) K').
    rewrite (cont_compose_snd_arg_let K' x  (transWork (add x0 (add x ns)) e2 (rLetHole x0 (fill_hole_r (App x x0) K)))).
    rewrite (IHe2 (add x0 (add x ns)) (rLetHole x0 (fill_hole_r (App x x0) K)) K').
    rewrite (cont_compose_snd_arg_let K' x0 (fill_hole_r (App x x0) K)).
    rewrite (cont_compose_fill_het_compose K' K (App x x0)).
    reflexivity.
  - fold transWork.
    rewrite (IHe1 ns (rLetHole x (transWork ns e2 K)) K').
    rewrite (cont_compose_snd_arg_let K' x (transWork ns e2 K)).
    rewrite (IHe2 ns K K'). reflexivity.
  - fold transWork.
    rewrite (IHe1 (add x ns)
        (rLetHole x
          (transWork (add x0 (add x ns)) e2
             (rLetHole x0
                (transWork (add x1 (add x0 (add x ns))) e3
                       (rLetHole x1 (fill_hole_r (Pair x x0 x1) K)))))) K').
    rewrite (cont_compose_snd_arg_let K' x
          (transWork (add x0 (add x ns)) e2
             (rLetHole x0
                (transWork (add x1 (add x0 (add x ns))) e3
                       (rLetHole x1 (fill_hole_r (Pair x x0 x1) K)))))).
    rewrite (IHe2 (add x0 (add x ns)) (rLetHole x0
                (transWork (add x1 (add x0 (add x ns))) e3
                       (rLetHole x1 (fill_hole_r (Pair x x0 x1) K)))) K').
    rewrite (cont_compose_snd_arg_let K' x0
            (transWork (add x1 (add x0 (add x ns))) e3
                   (rLetHole x1 (fill_hole_r (Pair x x0 x1) K)))).
    rewrite (IHe3 (add x1 (add x0 (add x ns)))
                  (rLetHole x1 (fill_hole_r (Pair x x0 x1) K)) K').
    rewrite (cont_compose_snd_arg_let K' x1 (fill_hole_r (Pair x x0 x1) K)).
    rewrite (cont_compose_fill_het_compose K' K (Pair x x0 x1)).
    reflexivity.
  - destruct (atom_fresh ns).
    destruct (atom_fresh (add x ns)).
    destruct (atom_fresh (add x0 (add x ns))).
    fold transWork.
    rewrite (IHe (add x ns) (rLetHole x (fill_hole_r (Fst x) K)) K').
    rewrite (cont_compose_snd_arg_let K' x (fill_hole_r (Fst x) K)).
    rewrite (cont_compose_fill_het_compose K' K (Fst x)).
    reflexivity.
  - destruct (atom_fresh ns).
    destruct (atom_fresh (add x ns)).
    destruct (atom_fresh (add x0 (add x ns))).
    fold transWork.
    rewrite (IHe (add x ns) (rLetHole x (fill_hole_r (Snd x) K)) K').
    rewrite (cont_compose_snd_arg_let K' x (fill_hole_r (Snd x) K)).
    rewrite (cont_compose_fill_het_compose K' K (Snd x)).
    reflexivity.
Qed.

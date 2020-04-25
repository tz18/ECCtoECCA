Require Import ECC.
Require Import ECCA_core ECCA_typing.
Require Import translator.

Fixpoint het_compose (K : ECCAcont) (M : ECCAconf) : ECCAconf :=
  match M with
  | Comp e => fill_hole_r e K
  | Let x N M' => Let x N (het_compose K M')
  end.

Fixpoint cont_compose (K : ECCAcont) (K' : ECCAcont) : ECCAcont :=
  match K' with
  | Hole => K
  | LetHole x M => LetHole x (het_compose K M)
  end.

(* I am losing my mind, why tf do I have to define the following *)

Lemma cont_compose_snd_arg_hole (K : ECCAcont) :
  (cont_compose K Hole) = K.
Proof.
  intros. destruct K; reflexivity.
Qed.

Lemma cont_compose_snd_arg_let (K : ECCAcont) (x : atom) (M : ECCAconf) :
  (cont_compose K (LetHole x M)) = LetHole x (het_compose K M).
Proof.
  intros. destruct K; reflexivity.
Qed.

(* This is a little more understandable *)

Lemma cont_compose_fill_het_compose (K K' : ECCAcont) (N : ECCAcomp) :
  (het_compose K (fill_hole_r N K')) = (fill_hole_r N (cont_compose K K')).
Proof.
  intros. destruct K'.
  + simpl. replace (cont_compose K Hole) with K. reflexivity.
    symmetry. apply cont_compose_snd_arg_hole.
  + simpl. replace (cont_compose K (LetHole x E)) with (LetHole x (het_compose K E)). reflexivity. symmetry. apply cont_compose_snd_arg_let.
Qed. 
                         
Lemma compositionality:
  forall (e : ECCexp) (ns : atoms) (K K' : ECCAcont),
  het_compose K' (trans ns e K) =
  (trans ns e (cont_compose K' K)).
Proof.
  intros e. induction e.
  - unfold trans; simpl.
    intros ns K K'.
    destruct (atom_fresh ns).
    destruct (atom_fresh (add x0 ns)).
    destruct (atom_fresh (add x1 (add x0 ns))).
    destruct K; destruct K'; simpl; reflexivity.
  - unfold trans; simpl.
    intros ns K K'.
    destruct (atom_fresh ns).
    destruct (atom_fresh (add x ns)).
    destruct (atom_fresh (add x0 (add x ns))).
    destruct K; destruct K'; simpl; reflexivity.
  - unfold trans; simpl.
    intros ns K K'.
    destruct (atom_fresh ns).
    destruct (atom_fresh (add x0 ns)).
    destruct (atom_fresh (add x1 (add x0 ns))).
    fold trans.
    destruct K; destruct K'; simpl; reflexivity.
  - unfold trans; simpl.
    intros ns K K'.
    destruct (atom_fresh ns).
    destruct (atom_fresh (add x0 ns)).
    destruct (atom_fresh (add x1 (add x0 ns))).
    fold trans.
    destruct K; destruct K'; simpl; reflexivity.
  - unfold trans; simpl.
    intros ns K K'.
    destruct (atom_fresh ns).
    destruct (atom_fresh (add x ns)).
    destruct (atom_fresh (add x0 (add x ns))).
    fold trans.
    rewrite (IHe1 (add x ns) (LetHole x (trans (add x0 (add x ns)) e2
                                               (LetHole x0 (fill_hole_r (App x x0) K)))) K').
    rewrite (cont_compose_snd_arg_let K' x  (trans (add x0 (add x ns)) e2 (LetHole x0 (fill_hole_r (App x x0) K)))).
    rewrite (IHe2 (add x0 (add x ns)) (LetHole x0 (fill_hole_r (App x x0) K)) K').
    rewrite (cont_compose_snd_arg_let K' x0 (fill_hole_r (App x x0) K)).
    rewrite (cont_compose_fill_het_compose K' K (App x x0)).
    reflexivity.
  - unfold trans; simpl.
    intros ns K K'.
    destruct (atom_fresh ns).
    destruct (atom_fresh (add x0 ns)).
    destruct (atom_fresh (add x1 (add x0 ns))).
    fold trans.
    rewrite (IHe1 ns (LetHole x (trans ns e2 K)) K').
    rewrite (cont_compose_snd_arg_let K' x (trans ns e2 K)).
    rewrite (IHe2 ns K K'). reflexivity.
  - unfold trans; simpl.
    intros ns K K'.
    destruct (atom_fresh ns).
    destruct (atom_fresh (add x0 ns)).
    destruct (atom_fresh (add x1 (add x0 ns))).
    fold trans.
    rewrite (cont_compose_fill_het_compose K' K (Sig x (trans ns e1 Hole) (trans ns e2 Hole))). reflexivity.
  - unfold trans; simpl.
    intros ns K K'.
    destruct (atom_fresh ns).
    destruct (atom_fresh (add x ns)).
    destruct (atom_fresh (add x0 (add x ns))).
    fold trans.
    rewrite (IHe1 (add x ns)
        (LetHole x
          (trans (add x0 (add x ns)) e2
             (LetHole x0
                (trans (add x1 (add x0 (add x ns))) e3
                       (LetHole x1 (fill_hole_r (Pair x x0 x1) K)))))) K').
    rewrite (cont_compose_snd_arg_let K' x
          (trans (add x0 (add x ns)) e2
             (LetHole x0
                (trans (add x1 (add x0 (add x ns))) e3
                       (LetHole x1 (fill_hole_r (Pair x x0 x1) K)))))).
    rewrite (IHe2 (add x0 (add x ns)) (LetHole x0
                (trans (add x1 (add x0 (add x ns))) e3
                       (LetHole x1 (fill_hole_r (Pair x x0 x1) K)))) K').
    rewrite (cont_compose_snd_arg_let K' x0
            (trans (add x1 (add x0 (add x ns))) e3
                   (LetHole x1 (fill_hole_r (Pair x x0 x1) K)))).
    rewrite (IHe3 (add x1 (add x0 (add x ns)))
                  (LetHole x1 (fill_hole_r (Pair x x0 x1) K)) K').
    rewrite (cont_compose_snd_arg_let K' x1 (fill_hole_r (Pair x x0 x1) K)).
    rewrite (cont_compose_fill_het_compose K' K (Pair x x0 x1)).
    reflexivity.
  - unfold trans; simpl.
    intros ns K K'.
    destruct (atom_fresh ns).
    destruct (atom_fresh (add x ns)).
    destruct (atom_fresh (add x0 (add x ns))).
    fold trans.
    rewrite (IHe (add x ns) (LetHole x (fill_hole_r (Fst x) K)) K').
    rewrite (cont_compose_snd_arg_let K' x (fill_hole_r (Fst x) K)).
    rewrite (cont_compose_fill_het_compose K' K (Fst x)).
    reflexivity.
  - unfold trans; simpl.
    intros ns K K'.
    destruct (atom_fresh ns).
    destruct (atom_fresh (add x ns)).
    destruct (atom_fresh (add x0 (add x ns))).
    fold trans.
    rewrite (IHe (add x ns) (LetHole x (fill_hole_r (Snd x) K)) K').
    rewrite (cont_compose_snd_arg_let K' x (fill_hole_r (Snd x) K)).
    rewrite (cont_compose_fill_het_compose K' K (Snd x)).
    reflexivity.
  - unfold trans; simpl.
    intros ns K K'.
    destruct (atom_fresh ns).
    destruct (atom_fresh (add x ns)).
    destruct (atom_fresh (add x0 (add x ns))).
    rewrite (cont_compose_fill_het_compose K' K Tru).
    reflexivity.
  - unfold trans; simpl.
    intros ns K K'.
    destruct (atom_fresh ns).
    destruct (atom_fresh (add x ns)).
    destruct (atom_fresh (add x0 (add x ns))).
    rewrite (cont_compose_fill_het_compose K' K Fls).
    reflexivity.
  - unfold trans; simpl.
    intros ns K K'.
    destruct (atom_fresh ns).
    destruct (atom_fresh (add x ns)).
    destruct (atom_fresh (add x0 (add x ns))).
    destruct (atom_fresh (add x0 (add x ns))).
    rewrite (cont_compose_fill_het_compose K' K Bool).
    reflexivity.
Qed.
    
    
      
    
    

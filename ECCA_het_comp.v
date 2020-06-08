Require Import ECC.
Require Import ECCA_core ECCA_typing.
Require Import translator.
Require Import ECCA_continuations.

Fixpoint het_compose_r {V: nat} (K : cont_r) (M : @ECCAconf V) : ECCAconf :=
  match M with
  | Comp e => fill_hole_r e K
  | Let N M' => Let N (@het_compose_r (S V) (wk_cont K) M')
  end.

Notation "K '<<' M '>>'" := (het_compose_r K M) (at level 250): ECCA_scope.

(* Fixpoint het_compose (K : cont_r) (M : ECCAexp) (p : IsANF M) : ECCAconf :=
  match M with
  | Comp e => fill_hole_r e K
  | Let x N M' => Let x N (het_compose K M')
  end. *)

Definition cont_compose {V: nat} (K : cont_r) (K' : cont_r) : @cont_r V :=
  match K' with
  | rHole => K
  | rLetHole M => rLetHole (het_compose_r (wk_cont K) M)
  end.

Notation "K1 '<<' K2 '>>'" := (cont_compose K1 K2) (at level 250): ECCA_scope.

(* This is a little more understandable 

Lemma technical_1 (K : cont_r) (e : ECCAcomp) (G : ECCAenv) :
(G |- (flattenECCAconf (fill_hole_r e K)) =e=
 (fill_hole (flattenECCAcomp e)
   (unrestrict_cont K)))%ECCA.
Proof. 
  induction K; auto.
Qed.
*)
Open Scope ECCA_scope.

Coercion flattenECCAconf: ECCAconf >-> ECCAexp.
Coercion flattenECCAcomp: ECCAcomp >-> ECCAexp.

Lemma cont_compose_fill_het_compose {V: nat} (K K' : cont_r) (N : ECCAcomp) :
  (het_compose_r K (fill_hole_r N K')) = (fill_hole_r N (@cont_compose V K K')).
Proof.
  intros. destruct K'; simpl; reflexivity.
Qed. 

Lemma naturality {V: nat} (K : cont_r) (M : ECCAconf) (G : ECCAenv) : 
  (ctx_empty |- (het_compose_r K M) =e= (fill_hole M (unrestrict_cont K)))%ECCA.
Proof.
induction M; try auto. 
+ simpl. apply technical_1.
+ simpl. destruct K.
  - simpl. induction het_compose_r.
    * unfold fill_hole in IHM. simpl in IHM. (* 
    *
  -
cut (G |- (eLet x A (het_compose_r K M)) =e=
            (subst x A (het_compose_r K M)))%ECCA. 
(* property of substitution *)
  cut (G |- (subst x A (het_compose_r K M)) =e=
            (fill_hole (subst x A M) (unrestrict_cont K)))%ECCA.
  (* by ??? *)
 cut (G |- (fill_hole (subst x A M) (unrestrict_cont K)) =e=
            (het_compose_r K (getECCAconf (subst x A M))))%ECCA.
 (* by some tedious property of substitution ??? *)
 cut (G |- (subst x A (fill_hole K M)) =e=
            (subst x A (het_compose_r K M)))%ECCA.
(* by IH *)
 cut (G |- (fill_hole K M) =e=
            (het_compose_r K M))%ECCA.
(* by zeta *)
  cut (G |-  (het_compose_r K (subst x A M)) =e=
fill_hole
   (eLet x (flattenECCAcomp A)
      (flattenECCAconf M))
   (unrestrict_cont K)
           ))%ECCA. *)
Admitted.


(*
Oof, fails in the first case when trying to fold transWork, can't seem to figure out the 
implicit parameter :,( *)

Lemma compositionality (e : ECCexp) (K K' : cont_r):
  het_compose_r K' (transWork e K) =
  (transWork e (@cont_compose 0 K' K)).
Proof.
  intros. induction e.
  all: unfold transWork; simpl.
  all: try (destruct K; destruct K'; simpl; reflexivity).
  - fold transWork.
  - fold transWork.
    rewrite (IHe1 (add x ns) (rLetHole x (transWork (add x0 (add x ns)) e2
                                               (rLetHole x0 (fill_hole_r (App x x0) K)))) K').
    simpl.
    rewrite (IHe2 (add x0 (add x ns)) (rLetHole x0 (fill_hole_r (App x x0) K)) K'). simpl.
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

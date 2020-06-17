Require Import ECC.
Require Import ECCA_core ECCA_core_lemmas ECCA_typing.
Require Import translator.
Require Import ECCA_continuations.
Require Import String.

Fixpoint het_compose_r {V: nat} (K : @cont_r V) (M : @ECCAconf V) {struct M} : ECCAconf :=
  match M with
  | Comp e => fill_hole_r e K
  | Let N M' => Let N (@het_compose_r (S V) (wk_cont K) M')
  | If V1 M1 M2 => If V1
                      (het_compose_r K M1)
                      (het_compose_r K M2)
  end.

Notation "K '<<' M '>>'" := (het_compose_r K M) (at level 250): ECCA_scope.

(* Fixpoint het_compose (K : cont_r) (M : ECCAexp) (p : IsANF M) : ECCAconf :=
  match M with
  | Comp e => fill_hole_r e K
  | Let x N M' => Let x N (het_compose K M')
  end. *)

Definition cont_compose {V: nat} (K : @cont_r V) (K' : @cont_r V) : @cont_r V :=
  match K' with
  | rHole => K
  | rLetHole M => rLetHole (het_compose_r (wk_cont K) M)
  end.

Notation "K1 '<<' K2 '>>'" := (cont_compose K1 K2) (at level 250): ECCA_scope.

(* This is a little more understandable  *)

Lemma technical_1 (K : cont_r) (e : ECCAcomp) (G : ECCAenv) :
(G |- (flattenECCAconf (fill_hole_r e K)) =e=
 (fill_hole (flattenECCAcomp e)
   (unrestrict_cont K)))%ECCA.
Proof. 
  induction K; cbn; eauto.
Qed.

Open Scope ECCA_scope.

Coercion flattenECCAconf: ECCAconf >-> ECCAexp.
Coercion flattenECCAcomp: ECCAcomp >-> ECCAexp.

Lemma cont_compose_fill_het_compose {V: nat} (K K' : cont_r) (N : ECCAcomp) :
  (het_compose_r K (fill_hole_r N K')) = (fill_hole_r N (@cont_compose V K K')).
Proof.
  intros. destruct K'; simpl; reflexivity.
Qed. 

Lemma cont_compose_empty_hole {V: nat} (M: ECCAconf) :
  (@het_compose_r V rHole M) = M.
Proof.
  induction M; unfold het_compose_r.
  - auto.
  - fold (@het_compose_r (S V)). unfold wk_cont. rewrite IHM. auto.
  - fold (@het_compose_r V). rewrite IHM1. rewrite IHM2. auto.
Qed.

Require Import Coq.Program.Equality.
Lemma naturality (K : cont_r) (M : ECCAconf) (G : ECCAenv) :
  (@ECCA_conf_wf 0 G M) ->
  (G |- (het_compose_r K M) =e= (fill_hole M (unrestrict_cont K)))%ECCA.
Proof.
  intros. induction H; destruct K.
  + simpl. apply aE_Equiv with (e:=e); apply R_Refl.
  + simpl. apply aE_Equiv with (e:= eLet e B); apply R_Refl.
  + simpl. rewrite (cont_compose_empty_hole m).
    apply aE_Equiv with (e:= eLet n m); apply R_Refl.
  + simpl. admit.
  + simpl. rewrite (cont_compose_empty_hole m1).
    rewrite (cont_compose_empty_hole m2).
    apply aE_Equiv with (e:= eIf (flattenECCAval v) m1 m2); apply R_Refl.
  + simpl. admit.

 (*   
dependent induction M; try auto. 
+ simpl. apply technical_1.
+ simpl. destruct K.
- unfold fill_hole. unfold wk_cont. rewrite (cont_compose_empty_hole M).
  apply aE_Equiv with (e:=eLet A M); apply R_Refl.
- unfold fill_hole. unfold wk_cont. Admitted.

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

Require Import String.
Lemma compositionality {V: nat} (e : ECCexp) (K K' : @cont_r V):
  het_compose_r K' (transWork e K) =
  (transWork e (@cont_compose V K' K)).
Proof.
  intros. induction e.
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

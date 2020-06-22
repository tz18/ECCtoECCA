Require Import ECC.
Require Import ECCA_core ECCA_core_lemmas ECCA_typing.
Require Import ECCA_equiv_lemmas.
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
  induction M; cbn.
  - auto.
  - rewrite IHM. auto.
  - fold (@het_compose_r V). rewrite IHM1. rewrite IHM2. auto.
Qed.

Lemma compat_let_equiv (g: ECCAenv) (e e': ECCAexp) (e1 e2 A: ECCAexp) (x: name) :
(* FIXME: Why don't we reduce e? *)
      (g |- e =e= e' ) -> 
      ((g & x ~ Def e A) |- (open x e1) =e= (open x e2) ) ->
      (g |- (eLet e e1)  =e= (eLet e' e2) ).
Admitted.

Require Import Coq.Program.Equality.
Parameter bind_conf : forall {v : nat}, (@ECCAcomp v) -> (@ECCAconf (S v)) -> (@ECCAconf v).
Lemma bind_coerce (n :ECCAcomp) (m:ECCAconf) : (flattenECCAconf (bind_conf n m) = (bind n m)).
Admitted.

Lemma delta_compat (g: ECCAenv) (e: ECCAexp) (e1 e2 A: ECCAexp) (x: name) :
  ((g & x ~ Def e A) |- (open x e1) =e= (open x e2)) ->
  (g |- (bind e e1) =e= (bind e e2)).
Admitted.

(*1. Zeta reduction on the left. 2. IH (rewrite K<<M''>> to K[M] on the left. 
3. On the right, use K_compat lemma, should have goal K[M][x :=n] \equiv K[M[x := n]] 
e -> e', then K[e] = K[e'] 
3. Have goal: Show K[M'][x := n] \equiv K[let x = n in M'] 
4. need lemma to show K[M][x :=n] \equiv K[M[x := n] *)

Lemma naturality (K : cont_r) (M : ECCAconf) (G : ECCAenv) :
  (@ECCA_conf_wf 0 G M) ->
  (G |- (het_compose_r K M) =e= (fill_hole M (unrestrict_cont K)))%ECCA.
Proof.
  intros. induction H.
  + destruct K; eauto.
  + unfold het_compose_r. fold (@het_compose_r (S (0 + 0))).
    assert (ECCA_Equiv g (flattenECCAconf (Let n (het_compose_r (wk_cont K) m))) (eLet n (fill_hole (flattenECCAconf m) (unrestrict_cont (wk_cont K))))).
    * admit.
    * eapply equiv_trans. apply H2.
      eapply aE_Equiv. eapply R_RedR. eapply R_Let. destruct K.
      simpl. eapply R_RedR. apply R_Let. simpl. eapply R_CongLet. fold bind. fold (@kleisli 1). eapply R_RedR. eapply R_Let. fold (@kleisli 1).
    erewrite compat_let_equiv.
    - eapply R_RedR.
(* ?e = (bind n (wk_cont K <<m>>)) *)
      apply R_Let.
    - fold (@flattenECCAconf (S (0+0)) (het_compose_r (wk_cont K) m)).
      fold (@flattenECCAcomp (0+0) n).
      assert ((bind (@flattenECCAcomp (0+0) n) (het_compose_r (wk_cont K) m)) = (het_compose_r K (bind_conf n m))).
      * assert ((@bind n (0 + 0) (het_compose_r (@wk_cont (0 + 0) K) m)) = (@bind n 0 (het_compose_r (@wk_cont (0 + 0) K) m))); auto. admit. (* rewrite <- H3.  rewrite H2. *)
      * cbn. cbn in H2. rewrite H2. fold (@unrestrict_cont 0 K). destruct K.
      ++ simpl. rewrite cont_compose_empty_hole. apply R_RedR. rewrite bind_coerce. apply R_Let.
      ++ simpl. eapply R_Trans.
        -- eapply R_CongLet. eapply R_RedR. apply R_Let. instantiate (1:=B). apply R_Refl. 
        -- eapply R_Trans. eapply R_RedR. eapply R_Let. cbn in *. rewrite <- H2. admit.

 + (* If case *)admit.
Admitted.



(* 

 destruct K; eauto. rewrite (cont_compose_empty_hole m).
    apply aE_Equiv with (e:= eLet n m); apply R_Refl.
  + simpl. cbn in *.
Check rLetHole. eapply aE_Equiv.
    Focus 2.
    - eapply R_RedR.
      eapply R_Let.
    -  unfold bind.
       eapply R_CongLet.
      
  + simpl. rewrite (cont_compose_empty_hole m1).
    rewrite (cont_compose_empty_hole m2).
    apply aE_Equiv with (e:= eIf (flattenECCAval v) m1 m2); apply R_Refl.
  + simpl. admit. *)

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

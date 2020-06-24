Require Import ECC.
Require Import ECCA_core ECCA_core_lemmas ECCA_typing.
Require Import ECCA_equiv_lemmas.
Require Import translator.
Require Import ECCA_continuations.
Require Import String.

Fixpoint het_compose {V: nat} (K : @cont V) (M : @ECCAexp V) {struct M} : ECCAexp :=
  match M with
  | eLet N M' => eLet N (@het_compose (S V) (wk_cont K) M')
  | eIf V1 M1 M2 => eIf V1
                      (het_compose K M1)
                      (het_compose K M2)
  | _ => fill_hole M K
  end.

Notation "K '<<' M '>>'" := (het_compose K M) (at level 250): ECCA_scope.

(* Fixpoint het_compose (K : cont_r) (M : ECCAexp) (p : IsANF M) : ECCAconf :=
  match M with
  | Comp e => fill_hole_r e K
  | Let x N M' => Let x N (het_compose K M')
  end. *)

Definition cont_compose {V: nat} (K : @cont V) (K' : @cont V) : @cont V :=
  match K' with
  | Hole => K
  | LetHole M => LetHole (het_compose (wk_cont K) M)
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

Lemma cont_compose_fill_het_compose {V: nat} (K K' : cont) (N : ECCAexp) :
isComp N  ->
  (het_compose K (fill_hole N K')) = (fill_hole N (@cont_compose V K K')).
Proof.
  intros. destruct K'. 
  + cbn. destruct H. destruct N; cbn in *; auto.
    - destruct (@no_comp_from_Let V N1 N2). rewrite H0 in H. discriminate. 
    - destruct (@no_comp_from_If V N1 N2 N3). rewrite H0 in H. discriminate.
  + cbn. reflexivity.
Qed. 

Lemma het_compose_empty_hole {V: nat} (M: ECCAexp) :
  (@het_compose V Hole M) = M.
Proof.
  induction M; cbn; auto.
  - rewrite IHM2. auto.
  - rewrite IHM2, IHM3. auto.
Qed.

Lemma K_compat (g: ECCAenv) (K : cont) (e1 e2 : ECCAexp) :
  (ECCA_RedClosR g e1 e2) ->
  (ECCA_Equiv g (fill_hole e1 K) (fill_hole e2 K)).
Proof.
  intros. destruct K.
  + simpl. eapply aE_Equiv. apply H. apply R_Refl.
  + simpl. eapply aE_Equiv. apply R_CongLet with (x:="x") (A:=Bool).
    apply H. apply R_Refl. apply R_Refl.
Qed.     

Lemma bind_commutes_over_fill_hole (g: ECCAenv) (K : cont) (n m : ECCAexp) :
  (ECCA_Equiv g (bind n (fill_hole m (wk_cont K))) (fill_hole (bind n m) K)).
Proof.
  destruct K.
  + simpl. eapply aE_Equiv; apply R_Refl.
  + simpl. simpl_term_eq. assert ((bind n (wk B)) = B).
    * simpl_term_eq.
    * rewrite H. eauto.
Qed.

Lemma fill_hole_over_branches (g: ECCAenv) (K : cont) (v: ECCAval) (m1 m2 : ECCAexp) :
  (ECCA_Equiv g (eIf v (fill_hole m1 K) (fill_hole m2 K)) (fill_hole (eIf v m1 m2) K)).
Proof.
  destruct K.
  + unfold unrestrict_cont. simpl. eapply aE_Equiv; apply R_Refl.
  + unfold unrestrict_cont. simpl. eapply aE_Equiv.
(* I think here we need to prove that since v is a val, it is either Tru Fls or some id *)
Admitted.

Lemma IH_naturality_let (g: ECCAenv) (K : cont) (n: ECCAcomp) (m : ECCAconf) (A: ECCAexp) (x: name):
  (ECCA_Equiv (g & x ~ Def n A) (het_compose K (open x m)) (fill_hole (open x m) K)) ->
  (ECCA_Equiv g (eLet n (het_compose (wk_cont K) m)) (eLet n (fill_hole m (wk_cont K)))).
Proof.
Admitted.

Lemma Let_reduction (g: ECCAenv) (x: name) (n A m e: ECCAexp) :
(g & x ~ (Def n A) |- open x m =r> e) -> 
(g |- eLet n m =r> e).
Proof.
intros. apply R_RedR. (* assert (e=bind n (wk e)). simpl_term_eq. rewrite H0. apply R_Let. *)
Abort.

Lemma IH_naturality_if (g: ECCAenv) (K : cont) (v: ECCAval) (m1 m2 : ECCAconf) (y: name):
  (ECCA_Equiv (g & y ~ Eq v eTru) (het_compose K m1) (fill_hole m1 K)) ->
  (ECCA_Equiv (g & y ~ Eq v eFls) (het_compose K m2) (fill_hole m2 K)) -> 
  (ECCA_Equiv g (eIf v (het_compose K m1) (het_compose K m2)) (eIf v (fill_hole m1 K) (fill_hole m2 K))).
Admitted. 

Lemma equiv_let_compositional (x: name) (g: ECCAenv) (n1 n2 A: @ECCAexp 0) (b1 b2: @ECCAexp (1)):
ECCA_Equiv g n1 n2 ->
ECCA_Equiv (g & x ~ (Def n1 A)) (open x b1) (open x b2) ->
ECCA_Equiv g (eLet n1 b1) (eLet n2 b2).
Proof.
Admitted.

Lemma equiv_let_strengthening (x: name) (g: ECCAenv) (n1 A: @ECCAexp 0) (b1 b2: @ECCAexp (1)):
ECCA_Equiv (g & x ~ (Def n1 A)) (open x b1) (open x b2) ->
ECCA_Equiv g (eLet n1 b1) (bind n1 b2).
Proof.
Admitted.
 
(*1. Zeta reduction on the left. 2. IH (rewrite K<<M''>> to K[M] on the left. 
3. On the right, use K_compat lemma, should have goal K[M][x :=n] \equiv K[M[x := n]] 
e -> e', then K[e] = K[e'] 
3. Have goal: Show K[M'][x := n] \equiv K[let x = n in M'] 
4. need lemma to show K[M][x :=n] \equiv K[M[x := n] *)

Lemma naturality (K : cont) (M : ECCAexp) (G : ECCAenv) :
  (@ECCA_wf 0 G M) ->
  (G |- (het_compose K M) =e= (fill_hole M K))%ECCA.
Proof.
  intros. induction H. 1,2,3,4,5,6,7,8,9,10,13,14,15: destruct K; eauto.
  + destruct K. 
    - cbn. rewrite het_compose_empty_hole. eauto.
    - cbn in *. eapply equiv_let_strengthening with (b2:= eLet m (wk B0)) in IHECCA_wf4.
      * instantiate (1:= (eLet m B0)). 

 unfold het_compose. fold (@het_compose (S (0 + 0))).
    assert (ECCA_Equiv g (eLet n (het_compose (wk_cont K) m)) (eLet n (fill_hole m (wk_cont K)))).
    * apply IH_naturality_let with (x:=x) (A:=A). apply IHECCA_conf_wf2.
    * eapply equiv_trans. apply H2.
      assert (ECCA_Equiv g (fill_hole (flattenECCAconf (Let n m)) (unrestrict_cont K)) (fill_hole (bind n m) (unrestrict_cont K))).
      ++ apply K_compat. apply R_RedR. apply R_Let.
      ++ apply equiv_sym. eapply equiv_trans. apply H3. apply equiv_sym.
         assert (ECCA_Equiv g (eLet n (fill_hole m (unrestrict_cont (wk_cont K)))) (bind n (fill_hole m (unrestrict_cont (wk_cont K))))).
         ** eapply aE_Equiv. apply R_RedR. apply R_Let. apply R_Refl.
         ** eapply equiv_trans. apply H4. apply bind_commutes_over_fill_hole.
  + unfold het_compose. fold (@het_compose (0 + 0)).
    assert (ECCA_Equiv g (flattenECCAconf (If v (het_compose K m1) (het_compose K m2))) (eIf v (fill_hole m1 (unrestrict_cont K)) (fill_hole m2 (unrestrict_cont K)))).
    * apply IH_naturality_if with (y:=y). apply IHECCA_conf_wf2. apply IHECCA_conf_wf3.
    * eapply equiv_trans. apply H3. apply fill_hole_over_branches.
Qed.

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

cut (G |- (eLet x A (het_compose K M)) =e=
            (subst x A (het_compose K M)))%ECCA. 
(* property of substitution *)
  cut (G |- (subst x A (het_compose K M)) =e=
            (fill_hole (subst x A M) (unrestrict_cont K)))%ECCA.
  (* by ??? *)
 cut (G |- (fill_hole (subst x A M) (unrestrict_cont K)) =e=
            (het_compose K (getECCAconf (subst x A M))))%ECCA.
 (* by some tedious property of substitution ??? *)
 cut (G |- (subst x A (fill_hole K M)) =e=
            (subst x A (het_compose K M)))%ECCA.
(* by IH *)
 cut (G |- (fill_hole K M) =e=
            (het_compose K M))%ECCA.
(* by zeta *)
  cut (G |-  (het_compose K (subst x A M)) =e=
fill_hole
   (eLet x (flattenECCAcomp A)
      (flattenECCAconf M))
   (unrestrict_cont K)
           ))%ECCA. *)

Require Import String.
Lemma compositionality {V: nat} (e : ECCexp) (K K' : @cont_r V):
  het_compose K' (transWork e K) =
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

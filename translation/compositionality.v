Require Import ECC.
Require Import ECCA.core ECCA.core_lemmas ECCA.typing ECCA.equiv_lemmas ECCA.continuations.
Require Import translator.
Require Import String.

Open Scope ECCA_scope.

Coercion unrestrict_conf: conf >-> exp.
Coercion unrestrict_comp: comp >-> exp.

Lemma cont_compose_fill_het_compose {V: nat} (K K' : cont_r) (N : comp) :
  (het_compose_r K (fill_hole_r N K')) = (fill_hole_r N (@cont_compose V K K')).
Proof.
  intros. destruct K'; simpl; reflexivity.
Qed. 

Lemma het_compose_empty_hole {V: nat} (M: conf) :
  (@het_compose_r V rHole M) = M.
Proof.
  induction M; cbn.
  - auto.
  - rewrite IHM. auto.
  - fold (@het_compose_r V). rewrite IHM1. rewrite IHM2. auto.
Qed.

Lemma K_compat (g: env) (K : cont_r) (e1 e2 : exp) :
  (RedClos g e1 e2) ->
  (Equiv g (fill_hole e1 (unrestrict_cont K))) (fill_hole e2 (unrestrict_cont K)).
Proof.
  intros. destruct K.
  + simpl. eapply aE_Step. apply H. apply R_Refl.
  + simpl. eapply aE_Step. apply R_CongLet with (x:="x") (A:=Bool).
    apply H. apply R_Refl. apply R_Refl.
Qed.     

Lemma bind_commutes_over_fill_hole (g: env) (K : cont_r) (n m : exp) :
  (Equiv g (bind n (fill_hole m (unrestrict_cont (wk_cont K)))) (fill_hole (bind n m) (unrestrict_cont K))).
Proof.
  destruct K.
  + simpl. eapply aE_Step; apply R_Refl.
  + simpl.
    assert (Equiv g (eLet (bind n m) B) (bind (bind n m) B)).
    * eapply aE_Step. apply R_RedR. apply R_Let. apply R_Refl.
    * apply equiv_sym. eapply equiv_trans. apply H. apply equiv_sym.
      (*don't think bind (bind n m) B = (bind n (bind m B)) *)
Admitted.

Lemma fill_hole_over_branches (g: env) (K : cont_r) (v: val) (m1 m2 : conf) :
  (Equiv g (eIf v (fill_hole m1 (unrestrict_cont K)) (fill_hole m2 (unrestrict_cont K))) (fill_hole (If v m1 m2) (unrestrict_cont K))).
Proof.
  destruct K.
  + unfold unrestrict_cont. simpl. eapply aE_Step; apply R_Refl.
  + unfold unrestrict_cont. simpl. eapply aE_Step.
(* I think here we need to prove that since v is a val, it is either Tru Fls or some id *)
Admitted.


Lemma IH_naturality_let (g: env) (K : cont_r) (n: comp) (m : conf) (A: exp) (x: name):
  (Equiv (g & x ~ Def n A) (het_compose_r K (open_conf x m)) (fill_hole (open_conf x m) (unrestrict_cont K))) ->
  (Equiv g (unrestrict_conf (Let n (het_compose_r (wk_cont K) m))) (eLet n (fill_hole (unrestrict_conf m) (unrestrict_cont (wk_cont K))))).
Proof.
Admitted.

Lemma IH_naturality_if (g: env) (K : cont_r) (v: val) (m1 m2 : conf) (y: name):
  (Equiv (g & y ~ Eq (unrestrict_val v) eTru) (het_compose_r K m1) (fill_hole m1 (unrestrict_cont K))) ->
  (Equiv (g & y ~ Eq (unrestrict_val v) eFls) (het_compose_r K m2) (fill_hole m2 (unrestrict_cont K))) -> 
  (Equiv g (unrestrict_conf (If v (het_compose_r K m1) (het_compose_r K m2))) (eIf v (fill_hole m1 (unrestrict_cont K)) (fill_hole m2 (unrestrict_cont K)))).
Admitted. 

(*1. Zeta reduction on the left. 2. IH (rewrite K<<M''>> to K[M] on the left. 
3. On the right, use K_compat lemma, should have goal K[M][x :=n] \equiv K[M[x := n]] 
e -> e', then K[e] = K[e'] 
3. Have goal: Show K[M'][x := n] \equiv K[let x = n in M'] 
4. need lemma to show K[M][x :=n] \equiv K[M[x := n] *)

Lemma naturality (K : cont_r) (M : conf) (G : env) :
  (@WellBound_conf 0 G M) ->
  (G |- (het_compose_r K M) =e= (fill_hole M (unrestrict_cont K)))%ECCA.
Proof.
  intros. induction H.
  + destruct K; eauto.
  + unfold het_compose_r. fold (@het_compose_r (S (0 + 0))).
    assert (Equiv g (unrestrict_conf (Let n (het_compose_r (wk_cont K) m))) (eLet n (fill_hole (unrestrict_conf m) (unrestrict_cont (wk_cont K))))).
    * apply IH_naturality_let with (x:=x) (A:=A). apply IHWellBound_conf2.
    * eapply equiv_trans. apply H2.
      assert (Equiv g (fill_hole (unrestrict_conf (Let n m)) (unrestrict_cont K)) (fill_hole (bind n m) (unrestrict_cont K))).
      ++ apply K_compat. apply R_RedR. apply R_Let.
      ++ apply equiv_sym. eapply equiv_trans. apply H3. apply equiv_sym.
         assert (Equiv g (eLet n (fill_hole m (unrestrict_cont (wk_cont K)))) (bind n (fill_hole m (unrestrict_cont (wk_cont K))))).
         ** eapply aE_Step. apply R_RedR. apply R_Let. apply R_Refl.
         ** eapply equiv_trans. apply H4. apply bind_commutes_over_fill_hole.
  + unfold het_compose_r. fold (@het_compose_r (0 + 0)).
    assert (Equiv g (unrestrict_conf (If v (het_compose_r K m1) (het_compose_r K m2))) (eIf v (fill_hole m1 (unrestrict_cont K)) (fill_hole m2 (unrestrict_cont K)))).
    * apply IH_naturality_if with (y:=y). apply IHWellBound_conf2. apply IHWellBound_conf3.
    * eapply equiv_trans. apply H3. apply fill_hole_over_branches.
Qed.

(*
Require Import String.
Lemma compositionality {V: nat} (e : ECCexp) (K K' : @cont_r V):
  het_compose_r K' (transWork e K) =
  (transWork e (@cont_compose V K' K)).
Proof.
  intros. induction e.
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
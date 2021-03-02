Require Import core core_lemmas typing.
Require Import equiv_lemmas.
Require Import continuations.
Require Import String. 

(* This is a little more understandable  *)

Lemma technical_1 (K : cont_r) (e : comp) (G : env) :
(G |- (unrestrict_conf (fill_hole_r e K)) =e=
 (fill_hole (unrestrict_comp e)
   (unrestrict_cont K)))%ECCA.
Proof. 
  induction K; cbn; eauto.
Qed.

Open Scope ECCA_scope.

Coercion unrestrict_conf: conf >-> exp.
Coercion unrestrict_comp: comp >-> exp.

Lemma cont_compose_fill_het_compose (x: name) (K K' : cont_r) (N : comp):
  (het_compose_r K (fill_hole_r N K') x) = (fill_hole_r N (cont_compose K K' x)).
Proof.
  intros. destruct K'.
+  cbn. auto. rewrite het_compose_r_equation.  reflexivity.
+  cbn. rewrite het_compose_r_equation. reflexivity.
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
  + simpl. eapply aE_Step. (* apply R_CongLet with (x:="x") (A:=Bool).
    apply H. apply R_Refl. apply R_Refl. *)
Admitted.     

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

(* Lemma naturality (K : cont_r) (M : conf) (G : env) :
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
 *)
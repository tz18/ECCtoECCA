Require Import core.

(* How do we unbox this result given that we have proven it is never None? Three ways!*)


(* Definition unoption_neq {T: Type}(e: option T) : e <> None -> T.
Proof.
intros. destruct e.
exact t.
contradiction.
Defined.

thanks to pgiarrusso in freenode/#coq

Definition unoption_sig {T: Type}(o: option T): {n: T | o = Some n } -> T.
Proof. intros.
destruct X. exact x.
Defined. *)

Definition unoption_ex {T: Type}(o : option T) : (exists (n : T), o = Some n) -> T.
Proof. intros.
destruct o.
exact t.
exfalso. destruct H. discriminate.
Defined.


Definition invertsval {V: nat} (e: @val V) :=
getval (flattenval e) = Some e.
Definition invertsconf {V: nat} (e: @conf V) :=
getconf (flattenconf e) = Some e.
Definition invertscomp {V: nat} (e: @comp V) :=
getcomp (flattencomp e) = Some e.

Lemma helper_val {V: nat}:
forall (v1: @val V),
match getconf (flattenval v1) with
    | Some (Comp (Val e)) => Some e
    | _ => None
    end = Some v1 
-> getconf(flattenval v1) = Some (Comp (Val v1)).
Proof. intros. destruct (getconf (flattenval v1)); try discriminate.
destruct c; try discriminate. destruct e; try discriminate. inversion H. reflexivity.
Defined.

(* TODO: should write an LTAC tactic that does this: simplifies equalities involving match *)
(* Ltac simplmatcheq:=
  (* repeat *) match goal with 
  | [ H:  match ?x with  
      | _ => ?b
      | _ => ?c
    end = ?v |- _ ] => idtac "hello"
  end. *)
Lemma helper_comp {V: nat}:
forall (v1: @comp V),
match getconf (flattencomp v1) with
    | Some (Comp e) => Some e
    | _ => None
    end = Some v1 
-> getconf(flattencomp v1) = Some (Comp v1).
Proof. intros. destruct (getconf (flattencomp v1)); try discriminate.
destruct c; try discriminate. destruct e; try discriminate; inversion H; reflexivity.
Defined.

Lemma get_inverts_flatten {V: nat}: 
   (forall (e: @val V), invertsval e) 
/\ (forall (e: @conf V), invertsconf e)
/\ (forall (e: @comp V), invertscomp e).
Proof. apply val_conf_comp_comb.
1,2,7,8,9: (intros; cbv; auto).
1,2,3: intros; unfold invertsval, invertsconf in *; cbn; unfold getval. 
+ cut (getconf (ePi (flattenconf A) (flattenconf B)) = Some (Comp (Val (Pi A B)))).
 - intros. rewrite H1. auto.
 - cbn. rewrite H. rewrite H0. auto.
+ cut (getconf (eAbs (flattenconf A) (flattenconf B)) = Some (Comp (Val (Abs A B)))).
 - intros. rewrite H1. auto.
 - cbn. rewrite H. rewrite H0. auto.
+ cut (getconf (eSig (flattenconf A) (flattenconf B)) = Some (Comp (Val (Sig A B)))).
 - intros. rewrite H1. auto.
 - cbn. rewrite H. rewrite H0. auto.
+ intros; unfold invertsval, invertsconf in *. 
   apply helper_val in H. apply helper_val in H0.
   unfold getval. cbn. rewrite H. rewrite H0.
   rewrite H1. auto.
+ intros. unfold invertscomp, invertsconf in *. apply helper_comp in H.
  cbn. auto.
+ intros. unfold invertscomp, invertsconf in *. apply helper_comp in H.
  cbn. rewrite H. rewrite H0. auto.
+ intros. unfold invertsconf, invertsval, invertscomp in *. cbn.
  apply helper_val in H. rewrite H. rewrite H0. rewrite H1. auto.
+ intros. unfold invertscomp, invertsval in *. apply helper_val in H.
  apply helper_val in H0. unfold getcomp.
  cbn. rewrite H. rewrite H0. auto.
+ intros; unfold invertscomp, invertsval in *; apply helper_val in H;
  unfold getcomp; cbn; rewrite H; auto.
+ intros; unfold invertscomp, invertsval in *; apply helper_val in H;
  unfold getcomp; cbn; rewrite H; auto.
+ intros; unfold invertscomp, invertsval in *; apply helper_val in H;
  unfold getcomp; cbn; rewrite H; auto.
Defined.

Definition reflectsval {V: nat} (e: @val V):=
isVal (flattenval e).
Definition reflectsconf {V: nat} (e: @conf V):=
isConf (flattenconf e).
Definition reflectscomp {V: nat} (e: @comp V):=
isComp (flattencomp e).

Lemma flatten_is_ANF {V: nat}:
   (forall (e: @val V), reflectsval e) 
/\ (forall (e: @conf V), reflectsconf e)
/\ (forall (e: @comp V), reflectscomp e).
Proof. repeat split. all: intros; exists e; apply get_inverts_flatten.
Defined.

Corollary flatten_conf_is_ANF {V: nat}:
(forall (e: @conf V), isConf (flattenconf e)).
Proof. apply flatten_is_ANF. Defined.

Corollary flatten_val_is_ANF {V: nat}:
(forall (e: @val V), isVal (flattenval e)).
Proof. apply flatten_is_ANF. Defined.

Corollary flatten_comp_is_ANF {V: nat}:
(forall (e: @comp V), isComp (flattencomp e)).
Proof. apply flatten_is_ANF. Defined.

Lemma wk_preserves_ANF {V: nat}:
forall (e: @exp V), 
(isVal e -> isVal (wk e))
/\ (isConf e -> isConf (wk e)) 
/\ (isComp e -> isComp (wk e)).
Proof. induction e.
+ repeat split.
  - intros.
    cbn. unfold isVal. exists (Id (wkv x)). auto.
  - intros. unfold isConf.
    cbn. exists (Comp (Val (Id (wkv x)))). auto.
  - intros.
    unfold isComp. cbn.
    exists (Val (Id (wkv x))). auto.
+ repeat split; cbv; eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2.
  destruct H0, H2.
  repeat split; intros.
  1: unfold getval; unfold getval in H5.
  3: unfold getcomp; unfold getcomp in H5. 
  all:  destruct H5; cbn in H5;
    destruct getconf eqn:Heq1 in H5; try discriminate;
    destruct getconf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2.
  destruct H0, H2.
  repeat split; intros.
  1: unfold getval; unfold getval in H5.
  3: unfold getcomp; unfold getcomp in H5. 
  all:  destruct H5; cbn in H5;
    destruct getconf eqn:Heq1 in H5; try discriminate;
    destruct getconf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2.
  destruct H0, H2.
  repeat split; intros.
  1: unfold getval; unfold getval in H5.
  3: unfold getcomp; unfold getcomp in H5. 
  all:  destruct H5; cbn in H5;
    destruct getconf eqn:Heq1 in H5; try discriminate;
    destruct getconf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2, IHe3.
  destruct H0, H2, H4.
  repeat split; intros.
  1: unfold getval in H8.
  3: unfold getcomp in H8.
  all:
    cbn in H8; destruct H8; 
    destruct getconf eqn:? in H8; try discriminate;
    destruct c eqn:? in H8; try discriminate;
    destruct e eqn:? in H8; try discriminate;
    subst;
    destruct getconf eqn:? in H8; try discriminate;
    destruct c eqn:? in H8; try discriminate;
    destruct e eqn:? in H8; try discriminate;
    subst;
    destruct getconf eqn:? in H8; try discriminate.
  1: unfold getval. 
  3: unfold getcomp. 
  all:
    cbn;
    unfold getval in H; destruct H; try rewrite Heqo; eauto;
    destruct getconf eqn:? in H ; try discriminate;
    destruct c0 eqn:? in H ; try discriminate;
    destruct e eqn:? in H ; try discriminate;
    subst; cbn in Heqo2; rewrite Heqo2;

    unfold getval in H1; destruct H1; try rewrite Heqo0; eauto;
    destruct getconf eqn:? in H1; try discriminate;
    destruct c0 eqn:? in H1; try discriminate;
    destruct e eqn:? in H1; try discriminate;
    subst; cbn in Heqo3; rewrite Heqo3;

    destruct H4; eauto; cbn in H4; rewrite H4; eauto.
+ repeat split; intros; cbn; (unfold isVal || unfold isConf || unfold isComp); cbn; eauto.
+ repeat split; intros; cbn; (unfold isVal || unfold isConf || unfold isComp); cbn; eauto.
+ repeat split; intros; cbn; (unfold isVal || unfold isConf || unfold isComp); cbn; eauto.
+ repeat split; intros; 
  destruct IHe1, IHe2; 
  destruct H1, H3;
  unfold isConf, isVal, isComp in *. 
  - unfold isVal; unfold getval; cbn. 
    destruct H. unfold getval in H. cbn in H.
    destruct getconf eqn:? in H; try discriminate.
    destruct c eqn:? in H; try discriminate.
    destruct getconf eqn:? in H; try discriminate.
  - cbn. 
    destruct H. cbn in H.
    destruct getconf eqn:? in H; try discriminate.
    destruct c eqn:? in H; try discriminate.
    subst.
    destruct getconf eqn:? in H; try discriminate.
   
    unfold getcomp in H4. rewrite Heqo in H4. 
    destruct H4; eauto. 
    destruct getconf eqn:? in H4; try discriminate.
    destruct c0 eqn:? in H4; try discriminate. subst.
    cbn in Heqo1. rewrite Heqo1.

    rewrite Heqo0 in H3. destruct H3; eauto.
    cbn in H3. rewrite H3. eauto.
  - unfold isComp; unfold getcomp; cbn. 
    destruct H. unfold getcomp in H. cbn in H.
    destruct getconf eqn:? in H; try discriminate.
    destruct c eqn:? in H; try discriminate.
    destruct getconf eqn:? in H; try discriminate.
+ repeat split; intros; destruct IHe1, IHe2, IHe3; destruct H1, H3, H5;
    unfold isConf, isVal, isComp in *. 
  1: unfold getval; unfold getval in H.
  3: unfold getcomp; unfold getcomp in H.
  all: cbn.
  all:  destruct H; unfold getval in H; cbn in H;
    destruct getconf eqn:? in H; try discriminate;
    destruct getconf eqn:? in H; try discriminate;
    destruct getconf eqn:? in H; try discriminate;
    destruct c1 eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate.
  - subst.
    rewrite Heqo in H3. destruct H3; eauto.
    cbn in H3. rewrite H3.
    rewrite Heqo0 in H5. destruct H5; eauto.
    cbn in H5. rewrite H5.
    unfold getval in H0. rewrite Heqo1 in H0. destruct H0; eauto.
    destruct getconf eqn:? in H0; try discriminate. 
    destruct c1 eqn:? in H0; try discriminate.
    destruct e eqn:? in H0; try discriminate.
    subst.
    cbn in Heqo2. rewrite Heqo2. eauto.
+ repeat split; intros; destruct IHe1, IHe2; destruct H1, H3;
  unfold isConf, isVal, isComp in *.
  3: unfold getcomp in H; unfold getcomp.
  1: unfold getval in H.
  all: destruct H; cbn in H;
    destruct getconf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate;
    subst;
    destruct getconf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate.
  all:
    subst; cbn;
    unfold getval in H0; rewrite Heqo in H0;  destruct H0; eauto; 
    destruct getconf eqn:? in H0; try discriminate; 
    destruct c eqn:? in H0; try discriminate;
    destruct e eqn:? in H0; try discriminate; subst;
    cbn in Heqo1; rewrite Heqo1;
    unfold getval in H2; rewrite Heqo0 in H2;  destruct H2; eauto; 
    destruct getconf eqn:? in H2; try discriminate; 
    destruct c eqn:? in H2; try discriminate;
    destruct e eqn:? in H2; try discriminate; subst;
    cbn in Heqo2; rewrite Heqo2; eauto.
+ repeat split; intros; destruct IHe; destruct H1;
  unfold isConf, isVal, isComp in *.
  1: unfold getval in H; unfold getval.
  3: unfold getcomp in H; unfold getcomp.
  all: cbn in H; destruct H; 
    destruct getconf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate.
  all: subst; cbn; unfold getval in H0; rewrite Heqo in H0; destruct H0; eauto;
    destruct getconf eqn:? in H0; try discriminate;
    destruct c eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate;
    subst; cbn in Heqo0; rewrite Heqo0; eauto.
+ repeat split; intros; destruct IHe; destruct H1;
  unfold isConf, isVal, isComp in *.
  1: unfold getval in H; unfold getval.
  3: unfold getcomp in H; unfold getcomp.
  all: cbn in H; destruct H; 
    destruct getconf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate.
  all: subst; cbn; unfold getval in H0; rewrite Heqo in H0; destruct H0; eauto;
    destruct getconf eqn:? in H0; try discriminate;
    destruct c eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate;
    subst; cbn in Heqo0; rewrite Heqo0; eauto.
Defined.

Corollary wk_preserves_conf {V: nat}: 
forall (e: @exp V), (isConf e -> isConf (wk e)).
Proof. apply wk_preserves_ANF. Defined.

Corollary wk_preserves_val {V: nat}: 
forall (e: @exp V), (isVal e -> isVal (wk e)).
Proof. apply wk_preserves_ANF. Defined.

Corollary wk_preserves_comp {V: nat}: 
forall (e: @exp V), (isComp e -> isComp (wk e)).
Proof. apply wk_preserves_ANF. Defined.

Compute (unoption_ex (getval (wk (flattenval (Tru))))) ((wk_preserves_val (flattenval (Tru))) (flatten_val_is_ANF Tru)).
Definition wk_val {V: nat}(e: @val V) :=
(unoption_ex (getval (wk (flattenval (e))))) ((wk_preserves_val (flattenval e)) (flatten_val_is_ANF e)).
Definition wk_comp {V: nat}(e: @comp V):=
(unoption_ex (getcomp (wk (flattencomp (e))))) ((wk_preserves_comp (flattencomp e)) (flatten_comp_is_ANF e)).
Definition wk_conf {V: nat}(e: @conf V):=
(unoption_ex (getconf (wk (flattenconf (e))))) ((wk_preserves_conf (flattenconf e)) (flatten_conf_is_ANF e)).

Lemma close_preserves_ANF {V: nat} (x: name):
forall (e: @exp V), 
(isVal e -> isVal (close x e))
/\ (isConf e -> isConf (close x e)) 
/\ (isComp e -> isComp (close x e)).
Proof. induction e.
+ repeat split.
  - intros.
    cbn. unfold isVal. exists (Id (closev x x0)). auto.
  - intros. unfold isConf.
    cbn. exists (Comp (Val (Id (closev x x0)))). auto.
  - intros.
    unfold isComp. cbn.
    exists (Val (Id (closev x x0))). auto.
+ repeat split; cbv; eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2.
  destruct H0, H2.
  repeat split; intros.
  1: unfold getval; unfold getval in H5.
  3: unfold getcomp; unfold getcomp in H5. 
  all:  destruct H5; cbn in H5;
    destruct getconf eqn:Heq1 in H5; try discriminate;
    destruct getconf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2.
  destruct H0, H2.
  repeat split; intros.
  1: unfold getval; unfold getval in H5.
  3: unfold getcomp; unfold getcomp in H5. 
  all:  destruct H5; cbn in H5;
    destruct getconf eqn:Heq1 in H5; try discriminate;
    destruct getconf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2.
  destruct H0, H2.
  repeat split; intros.
  1: unfold getval; unfold getval in H5.
  3: unfold getcomp; unfold getcomp in H5. 
  all:  destruct H5; cbn in H5;
    destruct getconf eqn:Heq1 in H5; try discriminate;
    destruct getconf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2, IHe3.
  destruct H0, H2, H4.
  repeat split; intros.
  1: unfold getval in H8.
  3: unfold getcomp in H8.
  all:
    cbn in H8; destruct H8; 
    destruct getconf eqn:? in H8; try discriminate;
    destruct c eqn:? in H8; try discriminate;
    destruct e eqn:? in H8; try discriminate;
    subst;
    destruct getconf eqn:? in H8; try discriminate;
    destruct c eqn:? in H8; try discriminate;
    destruct e eqn:? in H8; try discriminate;
    subst;
    destruct getconf eqn:? in H8; try discriminate.
  1: unfold getval. 
  3: unfold getcomp.
  all:
    cbn;
    unfold getval in H; destruct H; try rewrite Heqo; eauto;
    destruct getconf eqn:? in H ; try discriminate;
    destruct c0 eqn:? in H ; try discriminate;
    destruct e eqn:? in H ; try discriminate;
    subst; cbn in Heqo2; rewrite Heqo2;

    unfold getval in H1; destruct H1; try rewrite Heqo0; eauto;
    destruct getconf eqn:? in H1; try discriminate;
    destruct c0 eqn:? in H1; try discriminate;
    destruct e eqn:? in H1; try discriminate;
    subst; cbn in Heqo3; rewrite Heqo3;

    destruct H4; eauto; cbn in H4; rewrite H4; eauto.
+ repeat split; intros; cbn; (unfold isVal || unfold isConf || unfold isComp); cbn; eauto.
+ repeat split; intros; cbn; (unfold isVal || unfold isConf || unfold isComp); cbn; eauto.
+ repeat split; intros; cbn; (unfold isVal || unfold isConf || unfold isComp); cbn; eauto.
+ repeat split; intros; 
  destruct IHe1, IHe2; 
  destruct H1, H3;
  unfold isConf, isVal, isComp in *. 
  - unfold isVal; unfold getval; cbn. 
    destruct H. unfold getval in H. cbn in H.
    destruct getconf eqn:? in H; try discriminate.
    destruct c eqn:? in H; try discriminate.
    destruct getconf eqn:? in H; try discriminate.
  - cbn. 
    destruct H. cbn in H.
    destruct getconf eqn:? in H; try discriminate.
    destruct c eqn:? in H; try discriminate.
    subst.
    destruct getconf eqn:? in H; try discriminate.
   
    unfold getcomp in H4. rewrite Heqo in H4. 
    destruct H4; eauto. 
    destruct getconf eqn:? in H4; try discriminate.
    destruct c0 eqn:? in H4; try discriminate. subst.
    cbn in Heqo1. rewrite Heqo1.

    rewrite Heqo0 in H3. destruct H3; eauto.
    cbn in H3. rewrite H3. eauto.
  - unfold isComp; unfold getcomp; cbn. 
    destruct H. unfold getcomp in H. cbn in H.
    destruct getconf eqn:? in H; try discriminate.
    destruct c eqn:? in H; try discriminate.
    destruct getconf eqn:? in H; try discriminate.
+ repeat split; intros; destruct IHe1, IHe2, IHe3; destruct H1, H3, H5;
    unfold isConf, isVal, isComp in *. 
  1: unfold getval; unfold getval in H.
  3: unfold getcomp; unfold getcomp in H.
  all: cbn.
  all:  destruct H; unfold getval in H; cbn in H;
    destruct getconf eqn:? in H; try discriminate;
    destruct getconf eqn:? in H; try discriminate;
    destruct getconf eqn:? in H; try discriminate;
    destruct c1 eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate.
  - subst.
    rewrite Heqo in H3. destruct H3; eauto.
    cbn in H3. rewrite H3.
    rewrite Heqo0 in H5. destruct H5; eauto.
    cbn in H5. rewrite H5.
    unfold getval in H0. rewrite Heqo1 in H0. destruct H0; eauto;
    destruct getconf eqn:? in H0; try discriminate;
    destruct c1 eqn:? in H0; try discriminate;
    destruct e eqn:? in H0; try discriminate.
    subst.
    cbn in Heqo2. rewrite Heqo2. eauto.
+ repeat split; intros; destruct IHe1, IHe2; destruct H1, H3;
  unfold isConf, isVal, isComp in *.
  3: unfold getcomp in H; unfold getcomp.
  1: unfold getval in H.
  all: destruct H; cbn in H;
    destruct getconf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate;
    subst;
    destruct getconf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate.
  all:
    subst; cbn;
    unfold getval in H0; rewrite Heqo in H0;  destruct H0; eauto; 
    destruct getconf eqn:? in H0; try discriminate; 
    destruct c eqn:? in H0; try discriminate;
    destruct e eqn:? in H0; try discriminate; subst;
    cbn in Heqo1; rewrite Heqo1;
    unfold getval in H2; rewrite Heqo0 in H2;  destruct H2; eauto; 
    destruct getconf eqn:? in H2; try discriminate; 
    destruct c eqn:? in H2; try discriminate;
    destruct e eqn:? in H2; try discriminate; subst;
    cbn in Heqo2; rewrite Heqo2; eauto.
+ repeat split; intros; destruct IHe; destruct H1;
  unfold isConf, isVal, isComp in *.
  1: unfold getval in H; unfold getval.
  3: unfold getcomp in H; unfold getcomp.
  all: cbn in H; destruct H; 
    destruct getconf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate.
  all: subst; cbn; unfold getval in H0; rewrite Heqo in H0; destruct H0; eauto;
    destruct getconf eqn:? in H0; try discriminate;
    destruct c eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate;
    subst; cbn in Heqo0; rewrite Heqo0; eauto.
+ repeat split; intros; destruct IHe; destruct H1;
  unfold isConf, isVal, isComp in *.
  1: unfold getval in H; unfold getval.
  3: unfold getcomp in H; unfold getcomp.
  all: cbn in H; destruct H; 
    destruct getconf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate.
  all: subst; cbn; unfold getval in H0; rewrite Heqo in H0; destruct H0; eauto;
    destruct getconf eqn:? in H0; try discriminate;
    destruct c eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate;
    subst; cbn in Heqo0; rewrite Heqo0; eauto.
Defined.

Corollary close_preserves_conf {V: nat} (x: name): 
forall (e: @exp V), (isConf e -> isConf (close x e)).
Proof. apply close_preserves_ANF. Defined.

Corollary close_preserves_val {V: nat} (x: name): 
forall (e: @exp V), (isVal e -> isVal (close x e)).
Proof. apply close_preserves_ANF. Defined.

Corollary close_preserves_comp {V: nat} (x: name): 
forall (e: @exp V), (isComp e -> isComp (close x e)).
Proof. apply close_preserves_ANF. Defined.

Definition close_val {V: nat}(x: name)(e: @val V) :=
(unoption_ex (getval (close x (flattenval (e))))) ((close_preserves_val x (flattenval e)) (flatten_val_is_ANF e)).
Definition close_comp {V: nat}(x: name)(e: @comp V):=
(unoption_ex (getcomp (close x (flattencomp (e))))) ((close_preserves_comp x (flattencomp e)) (flatten_comp_is_ANF e)).
Definition close_conf {V: nat}(x: name)(e: @conf V):=
(unoption_ex (getconf (close x (flattenconf (e))))) ((close_preserves_conf x (flattenconf e)) (flatten_conf_is_ANF e)).


Require Import Coq.Program.Equality.

Lemma open_preserves_ANF {V: nat} (x: name):
forall (e: @exp (S V)), 
(@isVal (S V) e -> @isVal V (open x e))
/\ (@isConf (S V) e -> @isConf V (open x e)) 
/\ (@isComp (S V) e -> @isComp V (open x e)).
Proof. dependent induction e.
+ repeat split.
  - intros.
    cbn. unfold isVal. exists (Id (openv x x0)). auto.
  - intros. unfold isConf.
    cbn. exists (Comp (Val (Id (openv x x0)))). auto.
  - intros.
    unfold isComp. cbn.
    exists (Val (Id (openv x x0))). auto.
+ repeat split; cbv; eauto.
+ intros. unfold isConf, isVal, isComp in *.
  destruct IHe1 with (V0:=V) (e0 := e1); auto.
  destruct IHe2  with (V0:=S V) (e0 := e2); auto.
  destruct H0, H2.
  repeat split; intros.
  1: unfold getval; unfold getval in H5.
  3: unfold getcomp; unfold getcomp in H5. 
  all: destruct H5; cbn in H5;
    destruct getconf eqn:Heq1 in H5; try discriminate;
    destruct getconf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  destruct IHe1 with (V0:=V) (e0 := e1); auto.
  destruct IHe2  with (V0:=S V) (e0 := e2); auto.
  destruct H0, H2.
  repeat split; intros.
  1: unfold getval; unfold getval in H5.
  3: unfold getcomp; unfold getcomp in H5. 
  all:  destruct H5; cbn in H5;
    destruct getconf eqn:Heq1 in H5; try discriminate;
    destruct getconf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  destruct IHe1 with (V0:=V) (e0 := e1); auto.
  destruct IHe2  with (V0:=S V) (e0 := e2); auto.
  destruct H0, H2.
  repeat split; intros.
  1: unfold getval; unfold getval in H5.
  3: unfold getcomp; unfold getcomp in H5. 
  all:  destruct H5; cbn in H5;
    destruct getconf eqn:Heq1 in H5; try discriminate;
    destruct getconf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  destruct IHe1 with (V0:=V) (e0 := e1); auto.
  destruct IHe2  with (V0:=V) (e0 := e2); auto.
  destruct IHe3  with (V0:=V) (e0 := e3); auto.
  destruct H0, H2, H4.
  repeat split; intros.
  1: unfold getval in H8.
  3: unfold getcomp in H8.
  all:
    cbn in H8; destruct H8; 
    destruct getconf eqn:? in H8; try discriminate.
    destruct c eqn:? in H8; try discriminate;
    destruct e eqn:? in H8; try discriminate;
    subst;
    destruct getconf eqn:? in H8; try discriminate;
    destruct c eqn:? in H8; try discriminate;
    destruct e eqn:? in H8; try discriminate;
    subst;
    destruct getconf eqn:? in H8; try discriminate.
  1: unfold getval. 
  3: unfold getcomp.
  all:
    cbn;
    unfold getval in H; destruct H; try rewrite Heqo; eauto;
    destruct getconf eqn:? in H ; try discriminate;
    destruct c0 eqn:? in H ; try discriminate;
    destruct e eqn:? in H ; try discriminate;
    subst; cbn in Heqo2; rewrite Heqo2;

    unfold getval in H1; destruct H1; try rewrite Heqo0; eauto;
    destruct getconf eqn:? in H1; try discriminate;
    destruct c0 eqn:? in H1; try discriminate;
    destruct e eqn:? in H1; try discriminate;
    subst; cbn in Heqo3; rewrite Heqo3;

    destruct H4; eauto; cbn in H4; rewrite H4; eauto.
+ repeat split; intros; cbn; (unfold isVal || unfold isConf || unfold isComp); cbn; eauto.
+ repeat split; intros; cbn; (unfold isVal || unfold isConf || unfold isComp); cbn; eauto.
+ repeat split; intros; cbn; (unfold isVal || unfold isConf || unfold isComp); cbn; eauto.
+ repeat split; intros; 
  destruct IHe1 with (V0:=V) (e0 := e1); auto;
  destruct IHe2  with (V0:=S V) (e0 := e2); auto;
  destruct H1, H3;
  unfold isConf, isVal, isComp in *. 
  - unfold isVal; unfold getval; cbn. 
    destruct H. unfold getval in H. cbn in H.
    destruct getconf eqn:? in H; try discriminate.
    destruct e eqn:? in H; try discriminate.
    destruct getconf eqn:? in H; try discriminate.
  - cbn. 
    destruct H. cbn in H.
    destruct getconf eqn:? in H; try discriminate.
    destruct e eqn:? in H; try discriminate.
    subst.
    destruct getconf eqn:? in H; try discriminate.
   
    unfold getcomp in H4. rewrite Heqo in H4. 
    destruct H4; eauto. 
    destruct getconf eqn:? in H4; try discriminate.
    destruct e3 eqn:? in H4; try discriminate. subst.
    cbn in Heqo1. rewrite Heqo1.

    rewrite Heqo0 in H3. destruct H3; eauto.
    cbn in H3. rewrite H3. eauto.
  - unfold isComp; unfold getcomp; cbn. 
    destruct H. unfold getcomp in H. cbn in H.
    destruct getconf eqn:? in H; try discriminate.
    destruct e eqn:? in H; try discriminate.
    destruct getconf eqn:? in H; try discriminate.
+ repeat split; intros; 
  destruct IHe1 with (V0:=V) (e0 := e1); auto;
  destruct IHe2  with (V0:= V) (e0 := e2); auto;
  destruct IHe3 with (V0:= V) (e0 := e3); auto;
  destruct H1, H3, H5;
    unfold isConf, isVal, isComp in *. 
  1: unfold getval; unfold getval in H.
  3: unfold getcomp; unfold getcomp in H.
  all: cbn.
  all:  destruct H; unfold getval in H; cbn in H;
    destruct getconf eqn:? in H; try discriminate;
    destruct getconf eqn:? in H; try discriminate;
    destruct getconf eqn:? in H; try discriminate;
    destruct e4 eqn:? in H; try discriminate;
    destruct e5 eqn:? in H; try discriminate.
  - subst.
    rewrite Heqo in H3. destruct H3; eauto.
    cbn in H3. rewrite H3.
    rewrite Heqo0 in H5. destruct H5; eauto.
    cbn in H5. rewrite H5.
    unfold getval in H0. rewrite Heqo1 in H0. destruct H0; eauto.
    destruct getconf eqn:? in H0; try discriminate. 
    destruct e4 eqn:? in H0; try discriminate.
    destruct e5 eqn:? in H0; try discriminate.
    subst.
    cbn in Heqo2. rewrite Heqo2. eauto.
+ repeat split; intros;
  destruct IHe1 with (V0:=V) (e0 := e1); auto;
  destruct IHe2  with (V0:=V) (e0 := e2); auto;
  destruct H1, H3;
  unfold isConf, isVal, isComp in *.
  3: unfold getcomp in H; unfold getcomp.
  1: unfold getval in H.
  all: destruct H; cbn in H;
    destruct getconf eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate;
    subst;
    destruct getconf eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate.
  all:
    subst; cbn;
    unfold getval in H0; rewrite Heqo in H0;  destruct H0; eauto; 
    destruct getconf eqn:? in H0; try discriminate; 
    destruct e eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate; subst;
    cbn in Heqo1; rewrite Heqo1;
    unfold getval in H2; rewrite Heqo0 in H2;  destruct H2; eauto; 
    destruct getconf eqn:? in H2; try discriminate; 
    destruct e eqn:? in H2; try discriminate;
    destruct e0 eqn:? in H2; try discriminate; subst;
    cbn in Heqo2; rewrite Heqo2; eauto.
+ repeat split; intros; 
  destruct IHe with (V0:=V) (e0 := e); auto;
  destruct H1;
  unfold isConf, isVal, isComp in *.
  1: unfold getval in H; unfold getval.
  3: unfold getcomp in H; unfold getcomp.
  all: cbn in H; destruct H; 
    destruct getconf eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate;
    destruct e1 eqn:? in H; try discriminate.
  all: subst; cbn; unfold getval in H0; rewrite Heqo in H0; destruct H0; eauto;
    destruct getconf eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate;
    destruct e1 eqn:? in H0; try discriminate;
    subst; cbn in Heqo0; rewrite Heqo0; eauto.
+ repeat split; intros; destruct IHe with (V0:=V) (e0 := e); auto;
  destruct H1;
  unfold isConf, isVal, isComp in *.
  1: unfold getval in H; unfold getval.
  3: unfold getcomp in H; unfold getcomp.
  all: cbn in H; destruct H; 
    destruct getconf eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate;
    destruct e1 eqn:? in H; try discriminate.
  all: subst; cbn; unfold getval in H0; rewrite Heqo in H0; destruct H0; eauto;
    destruct getconf eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate;
    destruct e1 eqn:? in H0; try discriminate;
    subst; cbn in Heqo0; rewrite Heqo0; eauto.
Defined.

Corollary open_preserves_conf {V: nat} (x: name): 
forall (e: @exp (S V)), (isConf e -> isConf (open x e)).
Proof. apply open_preserves_ANF. Defined.

Corollary open_preserves_val {V: nat} (x: name): 
forall (e: @exp (S V)), (isVal e -> isVal (open x e)).
Proof. apply open_preserves_ANF. Defined.

Corollary open_preserves_comp {V: nat} (x: name): 
forall (e: @exp (S V)), (isComp e -> isComp (open x e)).
Proof. apply open_preserves_ANF. Defined.

Definition open_val {V: nat}(x: name)(e: @val (S V)) :=
(unoption_ex (getval (open x (flattenval (e))))) ((open_preserves_val x (flattenval e)) (flatten_val_is_ANF e)).
Definition open_comp {V: nat}(x: name)(e: @comp (S V)):=
(unoption_ex (getcomp (open x (flattencomp (e))))) ((open_preserves_comp x (flattencomp e)) (flatten_comp_is_ANF e)).
Definition open_conf {V: nat}(x: name)(e: @conf (S V)):=
(unoption_ex (getconf (open x (flattenconf (e))))) ((open_preserves_conf x (flattenconf e)) (flatten_conf_is_ANF e)).

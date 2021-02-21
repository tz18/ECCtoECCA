Require Import core.

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
  1: unfold restrict_val; unfold restrict_val in H5.
  3: unfold restrict_comp; unfold restrict_comp in H5. 
  all:  destruct H5; cbn in H5;
    destruct restrict_conf eqn:Heq1 in H5; try discriminate;
    destruct restrict_conf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2.
  destruct H0, H2.
  repeat split; intros.
  1: unfold restrict_val; unfold restrict_val in H5.
  3: unfold restrict_comp; unfold restrict_comp in H5. 
  all:  destruct H5; cbn in H5;
    destruct restrict_conf eqn:Heq1 in H5; try discriminate;
    destruct restrict_conf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2.
  destruct H0, H2.
  repeat split; intros.
  1: unfold restrict_val; unfold restrict_val in H5.
  3: unfold restrict_comp; unfold restrict_comp in H5. 
  all:  destruct H5; cbn in H5;
    destruct restrict_conf eqn:Heq1 in H5; try discriminate;
    destruct restrict_conf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2, IHe3.
  destruct H0, H2, H4.
  repeat split; intros.
  1: unfold restrict_val in H8.
  3: unfold restrict_comp in H8.
  all:
    cbn in H8; destruct H8; 
    destruct restrict_conf eqn:? in H8; try discriminate;
    destruct c eqn:? in H8; try discriminate;
    destruct e eqn:? in H8; try discriminate;
    subst;
    destruct restrict_conf eqn:? in H8; try discriminate;
    destruct c eqn:? in H8; try discriminate;
    destruct e eqn:? in H8; try discriminate;
    subst;
    destruct restrict_conf eqn:? in H8; try discriminate.
  1: unfold restrict_val. 
  3: unfold restrict_comp. 
  all:
    cbn;
    unfold restrict_val in H; destruct H; try rewrite Heqo; eauto;
    destruct restrict_conf eqn:? in H ; try discriminate;
    destruct c0 eqn:? in H ; try discriminate;
    destruct e eqn:? in H ; try discriminate;
    subst; cbn in Heqo2; rewrite Heqo2;

    unfold restrict_val in H1; destruct H1; try rewrite Heqo0; eauto;
    destruct restrict_conf eqn:? in H1; try discriminate;
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
  - unfold isVal; unfold restrict_val; cbn. 
    destruct H. unfold restrict_val in H. cbn in H.
    destruct restrict_conf eqn:? in H; try discriminate.
    destruct c eqn:? in H; try discriminate.
    destruct restrict_conf eqn:? in H; try discriminate.
  - cbn. 
    destruct H. cbn in H.
    destruct restrict_conf eqn:? in H; try discriminate.
    destruct c eqn:? in H; try discriminate.
    subst.
    destruct restrict_conf eqn:? in H; try discriminate.
   
    unfold restrict_comp in H4. rewrite Heqo in H4. 
    destruct H4; eauto. 
    destruct restrict_conf eqn:? in H4; try discriminate.
    destruct c0 eqn:? in H4; try discriminate. subst.
    cbn in Heqo1. rewrite Heqo1.

    rewrite Heqo0 in H3. destruct H3; eauto.
    cbn in H3. rewrite H3. eauto.
  - unfold isComp; unfold restrict_comp; cbn. 
    destruct H. unfold restrict_comp in H. cbn in H.
    destruct restrict_conf eqn:? in H; try discriminate.
    destruct c eqn:? in H; try discriminate.
    destruct restrict_conf eqn:? in H; try discriminate.
+ repeat split; intros; destruct IHe1, IHe2, IHe3; destruct H1, H3, H5;
    unfold isConf, isVal, isComp in *. 
  1: unfold restrict_val; unfold restrict_val in H.
  3: unfold restrict_comp; unfold restrict_comp in H.
  all: cbn.
  all:  destruct H; unfold restrict_val in H; cbn in H;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct c1 eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate.
  - subst.
    rewrite Heqo in H3. destruct H3; eauto.
    cbn in H3. rewrite H3.
    rewrite Heqo0 in H5. destruct H5; eauto.
    cbn in H5. rewrite H5.
    unfold restrict_val in H0. rewrite Heqo1 in H0. destruct H0; eauto.
    destruct restrict_conf eqn:? in H0; try discriminate. 
    destruct c1 eqn:? in H0; try discriminate.
    destruct e eqn:? in H0; try discriminate.
    subst.
    cbn in Heqo2. rewrite Heqo2. eauto.
+ repeat split; intros; destruct IHe1, IHe2; destruct H1, H3;
  unfold isConf, isVal, isComp in *.
  3: unfold restrict_comp in H; unfold restrict_comp.
  1: unfold restrict_val in H.
  all: destruct H; cbn in H;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate;
    subst;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate.
  all:
    subst; cbn;
    unfold restrict_val in H0; rewrite Heqo in H0;  destruct H0; eauto; 
    destruct restrict_conf eqn:? in H0; try discriminate; 
    destruct c eqn:? in H0; try discriminate;
    destruct e eqn:? in H0; try discriminate; subst;
    cbn in Heqo1; rewrite Heqo1;
    unfold restrict_val in H2; rewrite Heqo0 in H2;  destruct H2; eauto; 
    destruct restrict_conf eqn:? in H2; try discriminate; 
    destruct c eqn:? in H2; try discriminate;
    destruct e eqn:? in H2; try discriminate; subst;
    cbn in Heqo2; rewrite Heqo2; eauto.
+ repeat split; intros; destruct IHe; destruct H1;
  unfold isConf, isVal, isComp in *.
  1: unfold restrict_val in H; unfold restrict_val.
  3: unfold restrict_comp in H; unfold restrict_comp.
  all: cbn in H; destruct H; 
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate.
  all: subst; cbn; unfold restrict_val in H0; rewrite Heqo in H0; destruct H0; eauto;
    destruct restrict_conf eqn:? in H0; try discriminate;
    destruct c eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate;
    subst; cbn in Heqo0; rewrite Heqo0; eauto.
+ repeat split; intros; destruct IHe; destruct H1;
  unfold isConf, isVal, isComp in *.
  1: unfold restrict_val in H; unfold restrict_val.
  3: unfold restrict_comp in H; unfold restrict_comp.
  all: cbn in H; destruct H; 
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate.
  all: subst; cbn; unfold restrict_val in H0; rewrite Heqo in H0; destruct H0; eauto;
    destruct restrict_conf eqn:? in H0; try discriminate;
    destruct c eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate;
    subst; cbn in Heqo0; rewrite Heqo0; eauto.
Defined.

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
  1: unfold restrict_val; unfold restrict_val in H5.
  3: unfold restrict_comp; unfold restrict_comp in H5. 
  all:  destruct H5; cbn in H5;
    destruct restrict_conf eqn:Heq1 in H5; try discriminate;
    destruct restrict_conf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2.
  destruct H0, H2.
  repeat split; intros.
  1: unfold restrict_val; unfold restrict_val in H5.
  3: unfold restrict_comp; unfold restrict_comp in H5. 
  all:  destruct H5; cbn in H5;
    destruct restrict_conf eqn:Heq1 in H5; try discriminate;
    destruct restrict_conf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2.
  destruct H0, H2.
  repeat split; intros.
  1: unfold restrict_val; unfold restrict_val in H5.
  3: unfold restrict_comp; unfold restrict_comp in H5. 
  all:  destruct H5; cbn in H5;
    destruct restrict_conf eqn:Heq1 in H5; try discriminate;
    destruct restrict_conf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  try destruct IHe1, IHe2, IHe3.
  destruct H0, H2, H4.
  repeat split; intros.
  1: unfold restrict_val in H8.
  3: unfold restrict_comp in H8.
  all:
    cbn in H8; destruct H8; 
    destruct restrict_conf eqn:? in H8; try discriminate;
    destruct c eqn:? in H8; try discriminate;
    destruct e eqn:? in H8; try discriminate;
    subst;
    destruct restrict_conf eqn:? in H8; try discriminate;
    destruct c eqn:? in H8; try discriminate;
    destruct e eqn:? in H8; try discriminate;
    subst;
    destruct restrict_conf eqn:? in H8; try discriminate.
  1: unfold restrict_val. 
  3: unfold restrict_comp.
  all:
    cbn;
    unfold restrict_val in H; destruct H; try rewrite Heqo; eauto;
    destruct restrict_conf eqn:? in H ; try discriminate;
    destruct c0 eqn:? in H ; try discriminate;
    destruct e eqn:? in H ; try discriminate;
    subst; cbn in Heqo2; rewrite Heqo2;

    unfold restrict_val in H1; destruct H1; try rewrite Heqo0; eauto;
    destruct restrict_conf eqn:? in H1; try discriminate;
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
  - unfold isVal; unfold restrict_val; cbn. 
    destruct H. unfold restrict_val in H. cbn in H.
    destruct restrict_conf eqn:? in H; try discriminate.
    destruct c eqn:? in H; try discriminate.
    destruct restrict_conf eqn:? in H; try discriminate.
  - cbn. 
    destruct H. cbn in H.
    destruct restrict_conf eqn:? in H; try discriminate.
    destruct c eqn:? in H; try discriminate.
    subst.
    destruct restrict_conf eqn:? in H; try discriminate.
   
    unfold restrict_comp in H4. rewrite Heqo in H4. 
    destruct H4; eauto. 
    destruct restrict_conf eqn:? in H4; try discriminate.
    destruct c0 eqn:? in H4; try discriminate. subst.
    cbn in Heqo1. rewrite Heqo1.

    rewrite Heqo0 in H3. destruct H3; eauto.
    cbn in H3. rewrite H3. eauto.
  - unfold isComp; unfold restrict_comp; cbn. 
    destruct H. unfold restrict_comp in H. cbn in H.
    destruct restrict_conf eqn:? in H; try discriminate.
    destruct c eqn:? in H; try discriminate.
    destruct restrict_conf eqn:? in H; try discriminate.
+ repeat split; intros; destruct IHe1, IHe2, IHe3; destruct H1, H3, H5;
    unfold isConf, isVal, isComp in *. 
  1: unfold restrict_val; unfold restrict_val in H.
  3: unfold restrict_comp; unfold restrict_comp in H.
  all: cbn.
  all:  destruct H; unfold restrict_val in H; cbn in H;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct c1 eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate.
  - subst.
    rewrite Heqo in H3. destruct H3; eauto.
    cbn in H3. rewrite H3.
    rewrite Heqo0 in H5. destruct H5; eauto.
    cbn in H5. rewrite H5.
    unfold restrict_val in H0. rewrite Heqo1 in H0. destruct H0; eauto;
    destruct restrict_conf eqn:? in H0; try discriminate;
    destruct c1 eqn:? in H0; try discriminate;
    destruct e eqn:? in H0; try discriminate.
    subst.
    cbn in Heqo2. rewrite Heqo2. eauto.
+ repeat split; intros; destruct IHe1, IHe2; destruct H1, H3;
  unfold isConf, isVal, isComp in *.
  3: unfold restrict_comp in H; unfold restrict_comp.
  1: unfold restrict_val in H.
  all: destruct H; cbn in H;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate;
    subst;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate.
  all:
    subst; cbn;
    unfold restrict_val in H0; rewrite Heqo in H0;  destruct H0; eauto; 
    destruct restrict_conf eqn:? in H0; try discriminate; 
    destruct c eqn:? in H0; try discriminate;
    destruct e eqn:? in H0; try discriminate; subst;
    cbn in Heqo1; rewrite Heqo1;
    unfold restrict_val in H2; rewrite Heqo0 in H2;  destruct H2; eauto; 
    destruct restrict_conf eqn:? in H2; try discriminate; 
    destruct c eqn:? in H2; try discriminate;
    destruct e eqn:? in H2; try discriminate; subst;
    cbn in Heqo2; rewrite Heqo2; eauto.
+ repeat split; intros; destruct IHe; destruct H1;
  unfold isConf, isVal, isComp in *.
  1: unfold restrict_val in H; unfold restrict_val.
  3: unfold restrict_comp in H; unfold restrict_comp.
  all: cbn in H; destruct H; 
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate.
  all: subst; cbn; unfold restrict_val in H0; rewrite Heqo in H0; destruct H0; eauto;
    destruct restrict_conf eqn:? in H0; try discriminate;
    destruct c eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate;
    subst; cbn in Heqo0; rewrite Heqo0; eauto.
+ repeat split; intros; destruct IHe; destruct H1;
  unfold isConf, isVal, isComp in *.
  1: unfold restrict_val in H; unfold restrict_val.
  3: unfold restrict_comp in H; unfold restrict_comp.
  all: cbn in H; destruct H; 
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct c eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate.
  all: subst; cbn; unfold restrict_val in H0; rewrite Heqo in H0; destruct H0; eauto;
    destruct restrict_conf eqn:? in H0; try discriminate;
    destruct c eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate;
    subst; cbn in Heqo0; rewrite Heqo0; eauto.
Defined.

Lemma open_preserves_ANF {V: nat} (x: name):
forall (e: @exp (S V)), 
(@isVal (S V) e -> @isVal V (open x e))
/\ (@isConf (S V) e -> @isConf V (open x e)) 
/\ (@isComp (S V) e -> @isComp V (open x e)).
Proof. Admitted. (* dependent induction e.
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
  1: unfold restrict_val; unfold restrict_val in H5.
  3: unfold restrict_comp; unfold restrict_comp in H5. 
  all: destruct H5; cbn in H5;
    destruct restrict_conf eqn:Heq1 in H5; try discriminate;
    destruct restrict_conf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  destruct IHe1 with (V0:=V) (e0 := e1); auto.
  destruct IHe2  with (V0:=S V) (e0 := e2); auto.
  destruct H0, H2.
  repeat split; intros.
  1: unfold restrict_val; unfold restrict_val in H5.
  3: unfold restrict_comp; unfold restrict_comp in H5. 
  all:  destruct H5; cbn in H5;
    destruct restrict_conf eqn:Heq1 in H5; try discriminate;
    destruct restrict_conf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  destruct IHe1 with (V0:=V) (e0 := e1); auto.
  destruct IHe2  with (V0:=S V) (e0 := e2); auto.
  destruct H0, H2.
  repeat split; intros.
  1: unfold restrict_val; unfold restrict_val in H5.
  3: unfold restrict_comp; unfold restrict_comp in H5. 
  all:  destruct H5; cbn in H5;
    destruct restrict_conf eqn:Heq1 in H5; try discriminate;
    destruct restrict_conf eqn:Heq2 in H5; try discriminate;
    cbn; destruct H0; eauto; destruct H2; eauto;
    cbn in H0, H2; rewrite H0, H2;
    eauto.
+ intros. unfold isConf, isVal, isComp in *. 
  destruct IHe1 with (V0:=V) (e0 := e1); auto.
  destruct IHe2  with (V0:=V) (e0 := e2); auto.
  destruct IHe3  with (V0:=V) (e0 := e3); auto.
  destruct H0, H2, H4.
  repeat split; intros.
  1: unfold restrict_val in H8.
  3: unfold restrict_comp in H8.
  all:
    cbn in H8; destruct H8; 
    destruct restrict_conf eqn:? in H8; try discriminate.
    destruct c eqn:? in H8; try discriminate;
    destruct e eqn:? in H8; try discriminate;
    subst;
    destruct restrict_conf eqn:? in H8; try discriminate;
    destruct c eqn:? in H8; try discriminate;
    destruct e eqn:? in H8; try discriminate;
    subst;
    destruct restrict_conf eqn:? in H8; try discriminate.
  1: unfold restrict_val. 
  3: unfold restrict_comp.
  all:
    cbn;
    unfold restrict_val in H; destruct H; try rewrite Heqo; eauto;
    destruct restrict_conf eqn:? in H ; try discriminate;
    destruct c0 eqn:? in H ; try discriminate;
    destruct e eqn:? in H ; try discriminate;
    subst; cbn in Heqo2; rewrite Heqo2;

    unfold restrict_val in H1; destruct H1; try rewrite Heqo0; eauto;
    destruct restrict_conf eqn:? in H1; try discriminate;
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
  - unfold isVal; unfold restrict_val; cbn. 
    destruct H. unfold restrict_val in H. cbn in H.
    destruct restrict_conf eqn:? in H; try discriminate.
    destruct e eqn:? in H; try discriminate.
    destruct restrict_conf eqn:? in H; try discriminate.
  - cbn. 
    destruct H. cbn in H.
    destruct restrict_conf eqn:? in H; try discriminate.
    destruct e eqn:? in H; try discriminate.
    subst.
    destruct restrict_conf eqn:? in H; try discriminate.
   
    unfold restrict_comp in H4. rewrite Heqo in H4. 
    destruct H4; eauto. 
    destruct restrict_conf eqn:? in H4; try discriminate.
    destruct e3 eqn:? in H4; try discriminate. subst.
    cbn in Heqo1. rewrite Heqo1.

    rewrite Heqo0 in H3. destruct H3; eauto.
    cbn in H3. rewrite H3. eauto.
  - unfold isComp; unfold restrict_comp; cbn. 
    destruct H. unfold restrict_comp in H. cbn in H.
    destruct restrict_conf eqn:? in H; try discriminate.
    destruct e eqn:? in H; try discriminate.
    destruct restrict_conf eqn:? in H; try discriminate.
+ repeat split; intros; 
  destruct IHe1 with (V0:=V) (e0 := e1); auto;
  destruct IHe2  with (V0:= V) (e0 := e2); auto;
  destruct IHe3 with (V0:= V) (e0 := e3); auto;
  destruct H1, H3, H5;
    unfold isConf, isVal, isComp in *. 
  1: unfold restrict_val; unfold restrict_val in H.
  3: unfold restrict_comp; unfold restrict_comp in H.
  all: cbn.
  all:  destruct H; unfold restrict_val in H; cbn in H;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct e4 eqn:? in H; try discriminate;
    destruct e5 eqn:? in H; try discriminate.
  - subst.
    rewrite Heqo in H3. destruct H3; eauto.
    cbn in H3. rewrite H3.
    rewrite Heqo0 in H5. destruct H5; eauto.
    cbn in H5. rewrite H5.
    unfold restrict_val in H0. rewrite Heqo1 in H0. destruct H0; eauto.
    destruct restrict_conf eqn:? in H0; try discriminate. 
    destruct e4 eqn:? in H0; try discriminate.
    destruct e5 eqn:? in H0; try discriminate.
    subst.
    cbn in Heqo2. rewrite Heqo2. eauto.
+ repeat split; intros;
  destruct IHe1 with (V0:=V) (e0 := e1); auto;
  destruct IHe2  with (V0:=V) (e0 := e2); auto;
  destruct H1, H3;
  unfold isConf, isVal, isComp in *.
  3: unfold restrict_comp in H; unfold restrict_comp.
  1: unfold restrict_val in H.
  all: destruct H; cbn in H;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate;
    subst;
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct e eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate.
  all:
    subst; cbn;
    unfold restrict_val in H0; rewrite Heqo in H0;  destruct H0; eauto; 
    destruct restrict_conf eqn:? in H0; try discriminate; 
    destruct e eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate; subst;
    cbn in Heqo1; rewrite Heqo1;
    unfold restrict_val in H2; rewrite Heqo0 in H2;  destruct H2; eauto; 
    destruct restrict_conf eqn:? in H2; try discriminate; 
    destruct e eqn:? in H2; try discriminate;
    destruct e0 eqn:? in H2; try discriminate; subst;
    cbn in Heqo2; rewrite Heqo2; eauto.
+ repeat split; intros; 
  destruct IHe with (V0:=V) (e0 := e); auto;
  destruct H1;
  unfold isConf, isVal, isComp in *.
  1: unfold restrict_val in H; unfold restrict_val.
  3: unfold restrict_comp in H; unfold restrict_comp.
  all: cbn in H; destruct H; 
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate;
    destruct e1 eqn:? in H; try discriminate.
  all: subst; cbn; unfold restrict_val in H0; rewrite Heqo in H0; destruct H0; eauto;
    destruct restrict_conf eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate;
    destruct e1 eqn:? in H0; try discriminate;
    subst; cbn in Heqo0; rewrite Heqo0; eauto.
+ repeat split; intros; destruct IHe with (V0:=V) (e0 := e); auto;
  destruct H1;
  unfold isConf, isVal, isComp in *.
  1: unfold restrict_val in H; unfold restrict_val.
  3: unfold restrict_comp in H; unfold restrict_comp.
  all: cbn in H; destruct H; 
    destruct restrict_conf eqn:? in H; try discriminate;
    destruct e0 eqn:? in H; try discriminate;
    destruct e1 eqn:? in H; try discriminate.
  all: subst; cbn; unfold restrict_val in H0; rewrite Heqo in H0; destruct H0; eauto;
    destruct restrict_conf eqn:? in H0; try discriminate;
    destruct e0 eqn:? in H0; try discriminate;
    destruct e1 eqn:? in H0; try discriminate;
    subst; cbn in Heqo0; rewrite Heqo0; eauto.
Defined. *)
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
restrict_val (unrestrict_val e) = Some e.
Definition invertsconf {V: nat} (e: @conf V) :=
restrict_conf (unrestrict_conf e) = Some e.
Definition invertscomp {V: nat} (e: @comp V) :=
restrict_comp (unrestrict_comp e) = Some e.

Lemma helper_val {V: nat}:
forall (v1: @val V),
match restrict_conf (unrestrict_val v1) with
    | Some (Comp (Val e)) => Some e
    | _ => None
    end = Some v1 
-> restrict_conf(unrestrict_val v1) = Some (Comp (Val v1)).
Proof. intros. destruct (restrict_conf (unrestrict_val v1)); try discriminate.
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
match restrict_conf (unrestrict_comp v1) with
    | Some (Comp e) => Some e
    | _ => None
    end = Some v1 
-> restrict_conf(unrestrict_comp v1) = Some (Comp v1).
Proof. intros. destruct (restrict_conf (unrestrict_comp v1)); try discriminate.
destruct c; try discriminate. destruct e; try discriminate; inversion H; reflexivity.
Defined.

Lemma restrict_unrestrict_id {V: nat}: 
   (forall (e: @val V), invertsval e) 
/\ (forall (e: @conf V), invertsconf e)
/\ (forall (e: @comp V), invertscomp e).
Proof. apply val_conf_comp_comb.
1,2,7,8,9: (intros; cbv; auto).
1,2,3: intros; unfold invertsval, invertsconf in *; cbn; unfold restrict_val. 
+ cut (restrict_conf (ePi (unrestrict_conf A) (unrestrict_conf B)) = Some (Comp (Val (Pi A B)))).
 - intros. rewrite H1. auto.
 - cbn. rewrite H. rewrite H0. auto.
+ cut (restrict_conf (eAbs (unrestrict_conf A) (unrestrict_conf B)) = Some (Comp (Val (Abs A B)))).
 - intros. rewrite H1. auto.
 - cbn. rewrite H. rewrite H0. auto.
+ cut (restrict_conf (eSig (unrestrict_conf A) (unrestrict_conf B)) = Some (Comp (Val (Sig A B)))).
 - intros. rewrite H1. auto.
 - cbn. rewrite H. rewrite H0. auto.
+ intros; unfold invertsval, invertsconf in *. 
   apply helper_val in H. apply helper_val in H0.
   unfold restrict_val. cbn. rewrite H. rewrite H0.
   rewrite H1. auto.
+ intros. unfold invertscomp, invertsconf in *. apply helper_comp in H.
  cbn. auto.
+ intros. unfold invertscomp, invertsconf in *. apply helper_comp in H.
  cbn. rewrite H. rewrite H0. auto.
+ intros. unfold invertsconf, invertsval, invertscomp in *. cbn.
  apply helper_val in H. rewrite H. rewrite H0. rewrite H1. auto.
+ intros. unfold invertscomp, invertsval in *. apply helper_val in H.
  apply helper_val in H0. unfold restrict_comp.
  cbn. rewrite H. rewrite H0. auto.
+ intros; unfold invertscomp, invertsval in *; apply helper_val in H;
  unfold restrict_comp; cbn; rewrite H; auto.
+ intros; unfold invertscomp, invertsval in *; apply helper_val in H;
  unfold restrict_comp; cbn; rewrite H; auto.
+ intros; unfold invertscomp, invertsval in *; apply helper_val in H;
  unfold restrict_comp; cbn; rewrite H; auto.
Defined.

Definition reflectsval {V: nat} (e: @val V):=
isVal (unrestrict_val e).
Definition reflectsconf {V: nat} (e: @conf V):=
isConf (unrestrict_conf e).
Definition reflectscomp {V: nat} (e: @comp V):=
isComp (unrestrict_comp e).

Lemma flatten_is_ANF {V: nat}:
   (forall (e: @val V), reflectsval e) 
/\ (forall (e: @conf V), reflectsconf e)
/\ (forall (e: @comp V), reflectscomp e).
Proof. repeat split. all: intros; exists e; apply restrict_unrestrict_id.
Defined.

Corollary flatten_conf_is_ANF {V: nat}:
(forall (e: @conf V), isConf (unrestrict_conf e)).
Proof. apply flatten_is_ANF. Defined.

Corollary flatten_val_is_ANF {V: nat}:
(forall (e: @val V), isVal (unrestrict_val e)).
Proof. apply flatten_is_ANF. Defined.

Corollary flatten_comp_is_ANF {V: nat}:
(forall (e: @comp V), isComp (unrestrict_comp e)).
Proof. apply flatten_is_ANF. Defined.

Lemma unrestrict_restrict_id {V: nat}: 
forall (e: @exp V),
  (forall (p: isConf e), 
    (unrestrict_conf ((unoption_ex (restrict_conf e)) p) ) = e)
  /\
  (forall (p: isComp e), 
    (unrestrict_comp ((unoption_ex (restrict_comp e)) p) ) = e)
  /\
  (forall (p: isVal e), 
    (unrestrict_val ((unoption_ex (restrict_val e)) p) ) = e).
Proof.
intros. induction e; split; auto.
+ intros. inversion p. inversion H. Admitted.

Corollary unrestrict_restrict_id_conf {V}:
forall (e: @exp V),
  (forall (p: isConf e), 
    (unrestrict_conf ((unoption_ex (restrict_conf e)) p) ) = e).
Proof. apply unrestrict_restrict_id. Defined.


(*===============================
=========--Names--===============
=================================*)

Require Export core_lemmas_names.

Corollary wk_preserves_conf {V: nat}: 
forall (e: @exp V), (isConf e -> isConf (wk e)).
Proof. apply wk_preserves_ANF. Defined.

Corollary wk_preserves_val {V: nat}: 
forall (e: @exp V), (isVal e -> isVal (wk e)).
Proof. apply wk_preserves_ANF. Defined.

Corollary wk_preserves_comp {V: nat}: 
forall (e: @exp V), (isComp e -> isComp (wk e)).
Proof. apply wk_preserves_ANF. Defined.

Compute (unoption_ex (restrict_val (wk (unrestrict_val (Tru))))) ((wk_preserves_val (unrestrict_val (Tru))) (flatten_val_is_ANF Tru)).
Definition wk_val {V: nat}(e: @val V) :=
(unoption_ex (restrict_val (wk (unrestrict_val (e))))) ((wk_preserves_val (unrestrict_val e)) (flatten_val_is_ANF e)).
Definition wk_comp {V: nat}(e: @comp V):=
(unoption_ex (restrict_comp (wk (unrestrict_comp (e))))) ((wk_preserves_comp (unrestrict_comp e)) (flatten_comp_is_ANF e)).
Definition wk_conf {V: nat}(e: @conf V):=
(unoption_ex (restrict_conf (wk (unrestrict_conf (e))))) ((wk_preserves_conf (unrestrict_conf e)) (flatten_conf_is_ANF e)).

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
(unoption_ex (restrict_val (close x (unrestrict_val (e))))) ((close_preserves_val x (unrestrict_val e)) (flatten_val_is_ANF e)).
Definition close_comp {V: nat}(x: name)(e: @comp V):=
(unoption_ex (restrict_comp (close x (unrestrict_comp (e))))) ((close_preserves_comp x (unrestrict_comp e)) (flatten_comp_is_ANF e)).
Definition close_conf {V: nat}(x: name)(e: @conf V):=
(unoption_ex (restrict_conf (close x (unrestrict_conf (e))))) ((close_preserves_conf x (unrestrict_conf e)) (flatten_conf_is_ANF e)).

Require Import Coq.Program.Equality.

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
(unoption_ex (restrict_val (open x (unrestrict_val (e))))) ((open_preserves_val x (unrestrict_val e)) (flatten_val_is_ANF e)).
Definition open_comp {V: nat}(x: name)(e: @comp (S V)):=
(unoption_ex (restrict_comp (open x (unrestrict_comp (e))))) ((open_preserves_comp x (unrestrict_comp e)) (flatten_comp_is_ANF e)).
Definition open_conf {V: nat}(x: name)(e: @conf (S V)):=
(unoption_ex (restrict_conf (open x (unrestrict_conf (e))))) ((open_preserves_conf x (unrestrict_conf e)) (flatten_conf_is_ANF e)).

(*
=====================================
=============--Size--================
=====================================
*)
Require Import Lia.
Require Import String Morph Var Context Relative.

Lemma esize_non_zero : forall V e, 0 < @esize V e.
Proof.
  induction e; simpl; lia.
Qed.

Lemma esize_open_id : forall {V: nat} (e: @exp (1 + V)) x, @esize (V) (open x e) = @esize (1 + V) e.
Proof. intros. 
  inductT e; induction V0; cbn; try easy; try (rewrite IHe1; try easy; rewrite IHe2; try easy; try (rewrite IHe3; try easy)).
  all: ( rewrite IHe; try easy).
Qed.

Lemma esize_close_id : forall {V: nat} (e: @exp (V)) x, @esize (1 + V) (close x e) = @esize (V) e.
Proof. intros. induction e; names; auto.
Qed.

Lemma esize_wk_id : forall {V: nat} (e: @exp (V)), @esize (1 + V) (wk e) = @esize (V) e.
Proof. intros. induction e; names; auto.
Qed.

Hint Resolve esize_open_id esize_close_id esize_wk_id.

Lemma unrestrict_open_commutes_conf (x: name) {V} (M: @conf (S V)): 
(@unrestrict_conf V (@open_conf V x M)) = (@open x V (@unrestrict_conf (S V) M)).
Proof.
unfold open_conf. apply unrestrict_restrict_id.
Qed.


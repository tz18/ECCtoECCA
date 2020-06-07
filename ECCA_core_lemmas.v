Require Import ECCA_core.

Definition invertsval {V: nat} (e: @ECCAval V) :=
getECCAval (flattenECCAval e) = Some e.
Definition invertsconf {V: nat} (e: @ECCAconf V) :=
getECCAconf (flattenECCAconf e) = Some e.
Definition invertscomp {V: nat} (e: @ECCAcomp V) :=
getECCAcomp (flattenECCAcomp e) = Some e.

Lemma helper_val {V: nat}:
forall (v1: @ECCAval V),
match getECCAconf (flattenECCAval v1) with
    | Some (Comp (Val e)) => Some e
    | _ => None
    end = Some v1 
-> getECCAconf(flattenECCAval v1) = Some (Comp (Val v1)).
Proof. intros. destruct (getECCAconf (flattenECCAval v1)); try discriminate.
+ destruct e; try discriminate. destruct e; try discriminate. inversion H. reflexivity.
Qed.

(* TODO: should write an LTAC tactic that does this: simplifies equalities involving match *)
(* Ltac simplmatcheq:=
  (* repeat *) match goal with 
  | [ H:  match ?x with  
      | _ => ?b
      | _ => ?c
    end = ?v |- _ ] => idtac "hello"
  end. *)
Lemma helper_comp {V: nat}:
forall (v1: @ECCAcomp V),
match getECCAconf (flattenECCAcomp v1) with
    | Some (Comp e) => Some e
    | _ => None
    end = Some v1 
-> getECCAconf(flattenECCAcomp v1) = Some (Comp v1).
Proof. intros. destruct (getECCAconf (flattenECCAcomp v1)); try discriminate.
+ destruct e; try discriminate. destruct e; try discriminate; inversion H; reflexivity.
Qed.

Lemma get_inverts_flatten {V: nat}: 
   (forall (e: @ECCAval V), invertsval e) 
/\ (forall (e: @ECCAconf V), invertsconf e)
/\ (forall (e: @ECCAcomp V), invertscomp e).
Proof. apply ECCA_val_conf_comp_comb.
1,2,7,8,9: (intros; cbv; auto).
1,2,3: intros; unfold invertsval, invertsconf in *; cbn; unfold getECCAval. 
+ cut (getECCAconf (ePi (flattenECCAconf A) (flattenECCAconf B)) = Some (Comp (Val (Pi A B)))).
 - intros. rewrite H1. auto.
 - cbn. rewrite H. rewrite H0. auto.
+ cut (getECCAconf (eAbs (flattenECCAconf A) (flattenECCAconf B)) = Some (Comp (Val (Abs A B)))).
 - intros. rewrite H1. auto.
 - cbn. rewrite H. rewrite H0. auto.
+ cut (getECCAconf (eSig (flattenECCAconf A) (flattenECCAconf B)) = Some (Comp (Val (Sig A B)))).
 - intros. rewrite H1. auto.
 - cbn. rewrite H. rewrite H0. auto.
+ intros; unfold invertsval, invertsconf in *. 
   apply helper_val in H. apply helper_val in H0.
   unfold getECCAval. cbn. rewrite H. rewrite H0.
   rewrite H1. auto.
+ intros. unfold invertscomp, invertsconf in *. apply helper_comp in H.
  cbn. auto.
+ intros. unfold invertscomp, invertsconf in *. apply helper_comp in H.
  cbn. rewrite H. rewrite H0. auto.
+ intros. unfold invertscomp, invertsval in *. apply helper_val in H.
  apply helper_val in H0. unfold getECCAcomp.
  cbn. rewrite H. rewrite H0. auto.
+ intros; unfold invertscomp, invertsval in *; apply helper_val in H;
  unfold getECCAcomp; cbn; rewrite H; auto.
+ intros; unfold invertscomp, invertsval in *; apply helper_val in H;
  unfold getECCAcomp; cbn; rewrite H; auto.
+ intros; unfold invertscomp, invertsval in *; apply helper_val in H;
  unfold getECCAcomp; cbn; rewrite H; auto.
Qed.

Definition reflectsval {V: nat} (e: @ECCAval V):=
isVal (flattenECCAval e).
Definition reflectsconf {V: nat} (e: @ECCAconf V):=
isANF (flattenECCAconf e).
Definition reflectscomp {V: nat} (e: @ECCAcomp V):=
isComp (flattenECCAcomp e).

Lemma flatten_is_ANF {V: nat}:
   (forall (e: @ECCAval V), reflectsval e) 
/\ (forall (e: @ECCAconf V), reflectsconf e)
/\ (forall (e: @ECCAcomp V), reflectscomp e).
Proof. repeat split. all: intros; exists e; apply get_inverts_flatten.
Qed.

Lemma wk_preserves_ANF {V: nat}:
forall (e: @ECCAexp V),
isANF e ->
isANF (wk e)
.
Proof. intros. induction e.
+ unfold isANF; cbn; eauto.
+ unfold isANF; cbn; eauto.
+ unfold isANF in *. 


  
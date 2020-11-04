Require Import core.
Require Import Coq.micromega.Lia.

Fixpoint trues {V: nat} (e: @exp V): nat:=
match e with
  | eId x => 0
  | eUni U => 0
  | ePi A B => (trues A) + (trues B)
  | eAbs A B => (trues A) + (trues B)
  | eSig A B => (trues A) + (trues B)
  | ePair v1 v2 A => (trues A) + (trues v1) + (trues v2)
  | eTru => 1
  | eFls => 0
  | eBool => 0
  | eLet A B => (trues A) + (trues B)
  | eIf v1 e1 e2 => (trues v1) + (trues e1) + (trues e2)
  | eApp v1 v2 => (trues v1) + (trues v2)
  | eFst v => trues v
  | eSnd v => trues v
end.

Fixpoint bools {V: nat} (e: @exp V): nat:=
match e with
  | eId x => 0
  | eUni U => 0
  | ePi A B => (bools A) + (bools B)
  | eAbs A B => (bools A) + (bools B)
  | eSig A B => (bools A) + (bools B)
  | ePair v1 v2 A => (bools A) + (bools v1) + (bools v2)
  | eTru => 1
  | eFls => 0
  | eBool => 0
  | eLet A B => (bools A) + (bools B)
  | eIf v1 e1 e2 => (bools v1) + (bools e1) + (bools e2)
  | eApp v1 v2 => (bools v1) + (bools v2)
  | eFst v => bools v
  | eSnd v => bools v
end.

Goal forall {V: nat}(e:@exp V), trues e <= bools e.
Proof.
intros.
induction e; intuition.
Qed.

Inductive trues_r {V: nat} : (@exp V) -> nat -> Prop :=
| t_tru:
  @trues_r V (eTru) 1
| t_id (x: atom):
  @trues_r V (eId x) 0
| t_uni (U: universe):
  @trues_r V (eUni U) 0
| t_fls:
  @trues_r V eFls 0
| t_bool:
  @trues_r V eBool 0
| t_fst (v: @exp V) (n: nat):
  trues_r v n ->
  @trues_r V (eFst v) n
| t_snd (v: @exp V) (n: nat):
  trues_r v n ->
  @trues_r V (eSnd v) n
| t_pi (A: exp) (B: @exp (S V)) (n3 n4: nat):
  trues_r A n3 ->
  @trues_r (S V) B n4 ->
  @trues_r V (ePi A B) (n3 + n4)
| t_abs (A: exp) (B: @exp (S V)) (n1 n2: nat):
  trues_r A n1 ->
  @trues_r (S V) B n2 ->
  @trues_r V (eAbs A B) (n1 + n2)
| t_sig (A: exp) (B: @exp (S V)) (n1 n2: nat):
  trues_r A n1 ->
  @trues_r (S V) B n2 ->
  @trues_r V (eSig A B) (n1 + n2)
| t_let (A: exp) (B: @exp (S V)) (n1 n2: nat):
  trues_r A n1 ->
  @trues_r (S V) B n2 ->
  @trues_r V (eLet A B) (n1 + n2)
| t_app (A B: exp) (n1 n2: nat):
  trues_r A n1 ->
  @trues_r V B n2 ->
  @trues_r V (eApp A B) (n1 + n2)
| t_pair (A v1 v2: exp) (n1 n2 n3: nat):
  trues_r A n1 ->
  trues_r v1 n2 ->
  trues_r v2 n3 ->
  @trues_r V (ePair v1 v2 A) (n1 + n2 + n3)
| t_if (v1 e1 e2: exp) (n1 n2 n3: nat):
  trues_r v1 n1 ->
  trues_r e1 n2 ->
  trues_r e2 n3 ->
  @trues_r V (eIf v1 e1 e2) (n1 + n2 + n3)
.

Inductive bools_r {V: nat} : (@exp V) -> nat -> Prop :=
| b_tru:
  @bools_r V (eTru) 1
| b_id (x: atom):
  @bools_r V (eId x) 0
| b_uni (U: universe):
  @bools_r V (eUni U) 0
| b_fls:
  @bools_r V eFls 1
| b_bool:
  @bools_r V eBool 0
| b_fst (v: @exp V) (n: nat):
  bools_r v n ->
  @bools_r V (eFst v) n
| b_snd (v: @exp V) (n: nat):
  bools_r v n ->
  @bools_r V (eSnd v) n
| b_pi (A: exp) (B: @exp (S V)) (n1 n2: nat):
  bools_r A n1 ->
  @bools_r (S V) B n2 ->
  @bools_r V (ePi A B) (n1 + n2)
| b_abs (A: exp) (B: @exp (S V)) (n1 n2: nat):
  bools_r A n1 ->
  @bools_r (S V) B n2 ->
  @bools_r V (eAbs A B) (n1 + n2)
| b_sig (A: exp) (B: @exp (S V)) (n1 n2: nat):
  bools_r A n1 ->
  @bools_r (S V) B n2 ->
  @bools_r V (eSig A B) (n1 + n2)
| b_let (A: exp) (B: @exp (S V)) (n1 n2: nat):
  bools_r A n1 ->
  @bools_r (S V) B n2 ->
  @bools_r V (eLet A B) (n1 + n2)
| b_app (A B: exp) (n1 n2: nat):
  bools_r A n1 ->
  @bools_r V B n2 ->
  @bools_r V (eApp A B) (n1 + n2)
| b_pair (A v1 v2: exp) (n1 n2 n3: nat):
  bools_r A n1 ->
  bools_r v1 n2 ->
  bools_r v2 n3 ->
  @bools_r V (ePair v1 v2 A) (n1 + n2 + n3)
| b_if (v1 e1 e2: exp) (n1 n2 n3: nat):
  bools_r v1 n1 ->
  bools_r e1 n2 ->
  bools_r e2 n3 ->
  @bools_r V (eIf v1 e1 e2) (n1 + n2 + n3)
.

Lemma boolsr_gte_truesr: forall {V:nat}, forall (e: @exp V) (n1 n2: nat), trues_r e n1 -> bools_r e n2 -> (n2 >= n1).
Proof. induction e; intros; inversion H; inversion H0; subst; auto.
+ cut (n0 >= n3). cut (n5 >= n4).
  lia. auto. auto.
+ cut (n4 >= n0). cut (n5 >= n3). lia. auto. auto.
+ cut (n4 >= n0). cut (n5 >= n3). lia. auto. auto.
+ cut (n5 >= n0). cut (n6 >= n3). cut (n7 >= n4). lia. all: auto.
+ cut (n4 >= n0). cut (n5 >= n3). lia. auto. auto.
+ cut (n5 >= n0). cut (n6 >= n3). cut (n7 >= n4). lia. all: auto.
+ cut (n4 >= n0). cut (n5 >= n3). lia. auto. auto.
Qed.

 Inductive trues_rg : env -> @exp 0 -> nat -> Prop :=
| t_trug (g: env):
  trues_rg g (eTru) 1
| t_idgdef (g: env) (e A: exp) (x: atom) (n: nat):
  has g x (Def e A) ->
  trues_rg g e n->
(*   trues_rg g A n'-> *)
  trues_rg g (eId x) n
| t_idgass (g: env) (A: exp) (x: atom) (n: nat):
  has g x (Assum A) ->
  trues_rg g A n->
  trues_rg g (eId x) n
| t_unig (g: env) (U: universe):
  trues_rg g (eUni U) 0
| t_flsg (g: env):
  trues_rg g eFls 0
| t_boolg (g: env):
  trues_rg g eBool 0
| t_fstg (v: exp) (n: nat) (g: env):
  trues_rg g v n ->
  trues_rg g (eFst v) n
| t_sndg (v: exp) (n: nat) (g: env):
  trues_rg g v n ->
  trues_rg g (eSnd v) n
| t_pig (A: exp) (B: @exp (S 0)) (x: name) (n: nat) (g: env):
  trues_rg (g & x ~ Assum A) (open x B) n ->
  trues_rg g (ePi A B) n
| t_absg (A: exp) (B: @exp (S 0)) (x: name) (n: nat) (g: env):
  trues_rg (g & x ~ Assum A) (open x B) n ->
  trues_rg g (eAbs A B) n
| t_sigg (A: exp) (B: @exp (S 0)) (x: name) (n: nat) (g: env):
  trues_rg (g & x ~ Assum A) (open x B) n ->
  trues_rg g (eSig A B) n
| t_letg (e A: exp) (B: @exp (S 0)) (x: name) (n: nat) (g: env):
  trues_rg (g & x ~ Def e A) (open x B) n ->
  trues_rg g (eLet e B) n
| t_appg (A B: exp) (n1 n2: nat) (g: env):
  trues_rg g A n1 ->
  trues_rg g B n2 ->
  trues_rg g (eApp A B) (n1 + n2)
| t_pairg (A v1 v2: exp) (n1 n2 n3: nat) (g: env):
  trues_rg g A n1 ->
  trues_rg g v1 n2 ->
  trues_rg g v2 n3 ->
  trues_rg g (ePair v1 v2 A) (n1 + n2 + n3)
| t_ifg (v1 e1 e2: exp) (n1 n2 n3: nat) (g: env):
  trues_rg g v1 n1 ->
  trues_rg g e1 n2 ->
  trues_rg g e2 n3 ->
  trues_rg g (eIf v1 e1 e2) (n1 + n2 + n3) 
.

Require Import String.
Open Scope string.
Goal trues_rg ctx_empty (eLet eTru (eAbs eFls eTru)) 1.
Proof. eapply t_letg. cbn. eapply t_absg. cbn. eapply t_trug. Unshelve. auto.
exact "X". exact "Y". Qed.


 Inductive bools_rg : env -> @exp 0 -> nat -> Prop :=
| b_trug (g: env):
  bools_rg g (eTru) 1
| b_idgdef (g: env) (e A: exp) (x: atom) (n: nat):
  has g x (Def e A) ->
  bools_rg g e n->
(*   bools_rg g A n'-> *)
  bools_rg g (eId x) n
| b_idgass (g: env) (A: exp) (x: atom) (n: nat):
  has g x (Assum A) ->
  bools_rg g A n->
  bools_rg g (eId x) n
| b_unig (g: env) (U: universe):
  bools_rg g (eUni U) 0
| b_flsg (g: env):
  bools_rg g eFls 1
| b_boolg (g: env):
  bools_rg g eBool 0
| b_fstg (v: exp) (n: nat) (g: env):
  bools_rg g v n ->
  bools_rg g (eFst v) n
| b_sndg (v: exp) (n: nat) (g: env):
  bools_rg g v n ->
  bools_rg g (eSnd v) n
| b_pig (A: exp) (B: @exp (S 0)) (x: name) (n: nat) (g: env):
  bools_rg (g & x ~ Assum A) (open x B) n ->
  bools_rg g (ePi A B) n
| b_absg (A: exp) (B: @exp (S 0)) (x: name) (n: nat) (g: env):
  bools_rg (g & x ~ Assum A) (open x B) n ->
  bools_rg g (eAbs A B) n
| b_sigg (A: exp) (B: @exp (S 0)) (x: name) (n: nat) (g: env):
  bools_rg (g & x ~ Assum A) (open x B) n ->
  bools_rg g (eSig A B) n
| b_letg (e A: exp) (B: @exp (S 0)) (x: name) (n: nat) (g: env):
  bools_rg (g & x ~ Def e A) (open x B) n ->
  bools_rg g (eLet e B) n
| b_appg (A B: exp) (n1 n2: nat) (g: env):
  bools_rg g A n1 ->
  bools_rg g B n2 ->
  bools_rg g (eApp A B) (n1 + n2)
| b_pairg (A v1 v2: exp) (n1 n2 n3: nat) (g: env):
  bools_rg g A n1 ->
  bools_rg g v1 n2 ->
  bools_rg g v2 n3 ->
  bools_rg g (ePair v1 v2 A) (n1 + n2 + n3)
| b_ifg (v1 e1 e2: exp) (n1 n2 n3: nat) (g: env):
  bools_rg g v1 n1 ->
  bools_rg g e1 n2 ->
  bools_rg g e2 n3 ->
  bools_rg g (eIf v1 e1 e2) (n1 + n2 + n3) 
.

Eval simpl in (has (ctx_empty & "X" ~ eBool) (free "X") eTru).

Lemma nothing_in_empty: forall {A}(x: @var 0) M, ((@ctx_empty A) ∋ x ~ M) = False.
Proof.
intros. cbn. reflexivity. Qed.
Require Import Coq.Program.Equality.

Lemma has_function {A} (g: @context A)(x: var) (M M': A): 
has g x M /\ has g x M' ->
M = M'.
Proof.
intros. destruct H. dependent induction g.
+ cbn in H. contradiction. 
+ cbn in H. cbn in H0. destruct (bindv (closev a x)).
  - apply IHg with (x:= v). auto. auto. 
  - subst. reflexivity.
Qed.

Require Import Coq.Program.Equality.
Lemma boolsrg_gte_truesrg: forall (g: env) (e: @exp 0)  (n1 n2: nat), trues_rg g e n1 -> bools_rg g e n2 -> (n2 >= n1).
Proof. intros. dependent induction H0; dependent induction H; auto; try contradiction; try discriminate.
+ cut ((Def e A) = (Def e0 A0)).
    * intro. inversion H3. subst. auto. 
    * apply has_function with (x0:=x) (g0:=g). auto.
+ 

dependent induction g; dependent induction e.
  - inversion H; inversion H0; subst; cbn in *; try contradiction.
  - inversion H; inversion H0; subst. auto.
  - inversion H; inversion H0; subst.

+ inversion H; inversion H0; subst; cbn in *; try contradiction.
+ inversion H; inversion H0; subst.
  - cut ((Def e A) = (Def e0 A0)).
    * intro. inversion H1. subst. 
    * apply has_function with (x0:=x) (g0:=g). auto. 



 






inversion H; inversion H0; subst; try lia; try discriminate. 
+ inversion H9. subst. cbn. 
 dependent induction e.
+ intros. inversion H; inversion H0. subst. 
  - 
+ cut (n0 >= n3). cut (n5 >= n4).
  lia. auto. auto.
+ cut (n4 >= n0). cut (n5 >= n3). lia. auto. auto.
+ cut (n4 >= n0). cut (n5 >= n3). lia. auto. auto.
+ cut (n5 >= n0). cut (n6 >= n3). cut (n7 >= n4). lia. all: auto.
+ cut (n4 >= n0). cut (n5 >= n3). lia. auto. auto.
+ cut (n5 >= n0). cut (n6 >= n3). cut (n7 >= n4). lia. all: auto.
+ cut (n4 >= n0). cut (n5 >= n3). lia. auto. auto.
Qed.




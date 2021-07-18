Require Import core.
Require Export Atom.
Require Export String Morph Var Context Relative.
(*
=====================================
=======--Type Environments--=========
=====================================
*)

Inductive ctxmem :=
| Assum (A: @exp 0)
| Def (e: @exp 0) (A: @exp 0).

Definition env := @context ctxmem.

Definition ren_mem r m:=
match m with
| Assum A => Assum ([r]A)
| Def e A => Def ([r]e) ([r]A)
end.
Hint Unfold ren_mem.
Notation "☊ r ☊ t" := (ren_mem r%ren t) (*☊ : \as*)
    (at level 60, right associativity) : term_scope.

Fixpoint shift_env a g:=
match g with
| ctx_empty => ctx_empty
| ctx_cons g b m => ctx_cons (shift_env a g) b (☊^a☊ m)
| ctx_dummy g x => ctx_dummy (shift_env a g) x
end.

Definition env_cons g a m:=
ctx_cons (shift_env a g) a m.

Notation "Γ & x ~ A" := (env_cons Γ x A) (at level 50).

Definition assumes (g: env) (x: atom) (A: exp) :=
(has g x (Assum A)) \/ (exists (e: exp), (has g x (Def e A))).
Hint Unfold assumes.

Definition forall_has Γ (P : var -> ctxmem -> Prop) :=
  (forall x a, Γ ∋ x ~ a -> P x a).

Lemma forall_has_cons {Γ : env}
      {P : var -> ctxmem -> Prop} {x a} :
  P (free x) a ->
  forall_has (shift_env x Γ) (fun y b => P (shiftv x y) b) ->
  forall_has (Γ & x ~ a) P.
Proof.
  intros Hp Hf y b.
  destruct (compare_vars x y).
   - cbn; autorewrite with rw_vars; cbn;
      intros; subst; auto.
   - cbn. names. auto. 
Qed.

Lemma forall_has_map {Γ : env}
      {P Q : var -> ctxmem -> Prop} :
  forall_has Γ P ->
  (forall x a, P x a -> Q x a) ->
  forall_has Γ Q.
Proof.
  unfold forall_has.
  auto.
Qed.

Inductive relates
  : env -> ren -> env -> Prop :=
  | relates_intro :
      forall (Γ Δ : env) (s : ren)
             (total : total s),
        forall_has Γ (fun v a => has Δ (applyt s total v) (☊s☊a)) ->
        relates Γ s Δ.

Definition relates_total
           {Γ Δ : env} {r : ren}
           (rl : relates Γ r Δ) :=
  match rl with
  | relates_intro _ _ _ rn _ => rn
  end.

Check relates_total.

Definition relates_contexts
           {Γ Δ : env} {r : ren}
           (rl : relates Γ r Δ) :=
  match rl in relates Γ r' Δ return
    (forall v a, has Γ v a ->
                 has Δ (applyt r' (relates_total rl) v) (☊r'☊a)) with
  | relates_intro _ _ _ _ cs => cs
end.

Notation "Γ =[ r ]=> Δ" :=
  (relates Γ (r)%ren Δ) (at level 60).

Lemma shifted_env_has_shifted_contents Γ:
forall_has Γ (fun y b => forall x, (shift_env x Γ) ∋ y ~ (☊^ x☊b)).
Proof.
unfold forall_has.
induction Γ.
+ auto.
+ intros. cbn. destruct (compare_vars a x).
  - cbn in H. names. names in H. subst. auto.
  - cbn in H. names. names in H. apply IHΓ. auto.
+ intros. cbn. destruct (compare_vars a x).
  -  names. names in H. auto.
  -  names. names in H. auto.
Qed.

Lemma shift_0_makes_free a v:
exists x, @shiftv a 0 v = free x.
Proof. intros. destruct v.
+ names. exists (shift_name a name). auto.
+ names in l. contradiction.
Qed.

Lemma has_inversion g x (A: ctxmem):
has g x A -> 
exists n, x = free n /\
((exists g', g = (ctx_cons g' n A)) \/ 
(exists g' y A' x', (g = ctx_cons g' y A') /\ ((bindv (closev y x)) = Some x') /\ (has g' x' A)) \/
(exists g' y x', (g = ctx_dummy g' y) /\ (bindv (closev y x)) = Some x' /\ (has g' x' A))).
Proof.
intros. destruct g.
+ contradiction.
+ cbn in H. destruct (compare_vars a x).
  - names in H. subst. exists a. split. auto. eauto.
  - names in H. pose shift_0_makes_free. 
    destruct e with (a:=a) (v:=v). split with (x:=x). split. auto.
    right. left. exists g. exists a. exists val. esplit. split. auto. split. auto. names. eauto. eauto.
+ cbn in H. destruct (compare_vars a x).
  - names in H. contradiction.
  - names in H. pose shift_0_makes_free. 
    destruct e with (a:=a) (v:=v). split with (x:=x). split. auto.
    right. right. exists g. exists a. names. eauto.
Qed.


Lemma synchronized_shifting_1 Γ:
forall_has Γ (fun y b => forall x, (ctx_dummy (shift_env x Γ) x) ∋ (@applyt (@exp 0) (^x)%ren I 0 y) ~ (☊^ x☊b)).
Proof.
unfold forall_has. 
induction Γ.
+ intros. contradiction.
+ intros. apply shifted_env_has_shifted_contents in H. names. apply H.
+ intros. apply shifted_env_has_shifted_contents in H. names. apply H.
Qed.

Lemma synchronized_shifting_2 Γ:
forall_has Γ (fun y b => forall x A, (ctx_cons (shift_env x Γ) x A) ∋ (@applyt (@exp 0) (^x)%ren I 0 y) ~ (☊^ x☊b)).
Proof.
unfold forall_has. 
induction Γ.
+ intros. contradiction.
+ intros. apply shifted_env_has_shifted_contents in H. names. apply H.
+ intros. apply shifted_env_has_shifted_contents in H. names. apply H.
Qed.

Lemma dummy_for_cons Γ:
forall x,
forall_has (ctx_dummy (shift_env x Γ) x) (fun y b => forall A, (ctx_cons (shift_env x Γ) x A) ∋ y ~ b).
Proof.
unfold forall_has. intros. 
induction Γ.
+ intros. cbn in H. destruct (compare_vars x x0); names in H; contradiction.
+ intros. apply has_inversion in H. destruct H. destruct H. destruct H0.
  - destruct H0. names. apply H.
+ intros. apply shifted_env_has_shifted_contents in H. names. apply H.
Qed.


Lemma ctx_shift:
  forall Γ Δ x (a : ctxmem) (r : ren),
    Γ =[r]=> Δ ->
    Γ =[r,, ^x]=> (Δ & x ~ a).
Proof.
  intros * H.
  destruct H as [? ? r rn H].
  apply relates_intro with (s := (r,, ^x)%ren) (total := rn).
  apply (forall_has_map H); intros y b. 
  cbn; names.  intros. eapply shifted_env_has_shifted_contents in H. eapply H. 
  shelve. 
Admitted.

Lemma ctx_has (g: env) (x: name) (a: ctxmem):
  (has (ctx_cons g x a) (free x) a).
Proof.
  unfold has. rewrite rw_closev_same. unfold bindv. auto.
Qed.

(* Defining "g,g'|-"
  Append environment g to environment g'*)
Fixpoint append (g g': env) :=
match g with
| ctx_empty => g'
| ctx_cons g'' x A => ctx_cons (append g'' (shift_env x g')) x A (*g'' is already shifted by x *)
| ctx_dummy g'' x => ctx_cons (append g'' (shift_env x g')) x A
end.

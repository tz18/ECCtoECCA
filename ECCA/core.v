Require Export Atom.
Require Import String Morph Var Context Relative.
(* 
=====================================
=======--ECCA Definition--=========== 
=====================================
*)

Declare Scope ECCA_scope.
Delimit Scope ECCA_scope with ECCA.

(* The flat / single sort grammar of our language *)
Inductive exp {V: nat}: Type :=
  | eId (x: @atom V)
  | eUni (U: universe)
  | ePi (A: exp) (B: @exp (S V))
  | eAbs (A: exp) (B: @exp (S V))
  | eSig (A: exp) (B: @exp (S V))
  | ePair (v1 v2: exp) (A: exp)
  | eTru
  | eFls
  | eBool
  | eLet (A: exp) (B: @exp (S V))
  | eIf (v: exp) (e1 e2: exp) 
  | eApp (v1 v2: exp)
  | eFst (v: exp)
  | eSnd (v: exp)
.

Hint Constructors exp.

(* Telling shifted names how our language has binders *)

Module ECCATerm <: Term.
  Definition term := @exp.
  Definition unit {N}: morph (@var) N (@term) N :=
    morph_inject (@eId).

  Fixpoint kleisli {N M} (f : morph (@var) N (@term) M) V t :=
      match t with
      | eId x => f V x
      | eAbs A e =>
        eAbs (kleisli f V A) (nset_push (kleisli f (S V) (nset_pop e)))
      | ePi A B =>
        ePi (kleisli f V A) (nset_push (kleisli f (S V) (nset_pop B)))
      | eLet e1 e2 =>
        eLet (kleisli f V e1) (nset_push (kleisli f (S V) (nset_pop e2)))
      | eSig A B =>
        eSig (kleisli f V A) (nset_push (kleisli f (S V) (nset_pop B)))
      | eApp e1 e2 =>
        eApp (kleisli f V e1) (kleisli f V e2)
      | ePair e1 e2 A =>
        ePair (kleisli f V e1) (kleisli f V e2) (kleisli f V A)
      | eIf v e1 e2 =>
        eIf (kleisli f V v) (kleisli f V e1) (kleisli f V e2)
      | eFst e => eFst (kleisli f V e)
      | eSnd e => eSnd (kleisli f V e)
      | eUni U => eUni U
      | eTru => eTru
      | eFls => eFls
      | eBool => eBool
      (*   | If (e e1 e2: ECCexp) *)
      end.

  Lemma left_identity :
    forall N M (f : morph (@var) N (@term) M) V t,
      kleisli f V (unit V t) = f V t.
  Proof. reflexivity. Qed.

  Lemma right_identity :
    forall N V (t : @term (N + V)),
      @kleisli N N unit V t = t.
  Proof.
    intros.
    inductT t; simplT; reflexivity.
  Qed.

  Lemma associativity :
      forall N M L
        (f : morph (@var) N (@term) M)
        (g : morph (@var) M (@term) L) V t,
        kleisli (fun V' t' => kleisli g V' (f V' t')) V t
        = kleisli g V (kleisli f V t).
    Proof.
      intros.
      inductT t; simplT; reflexivity.
    Qed.

  Lemma unit_extend :
    forall N V v,
      morph_extend (@unit N) V v = unit V v.
  Proof.
    intros.
    apply morph_extend_inject.
  Qed.

  Lemma kleisli_extend :
    forall N M (f : morph (@var) N (@term) M) V t,
      morph_extend (kleisli f) V t
      = kleisli (morph_extend f) V t.
  Proof.
    intros.
    inductT t; simplT; reflexivity.
  Qed.      

  Lemma extensional :
    forall N M (f g : morph (@var) N (@term) M) V t,
      (forall V t, f V t = g V t) ->
      kleisli f V t = kleisli g V t.
  Proof.
    intros.
    inductT t; simplT; auto.
  Qed.

End ECCATerm.

Module ECCARen := Renamings(ECCATerm).
Export ECCATerm.
Export ECCARen.

(*
=====================================
=============--Size--================
=====================================
*)

Fixpoint esize {V: nat} (e: @exp V) : nat :=
  match e with
  | eId _ => 1
  | eUni _ => 1
  | ePi A B => 1 + (esize A) + (esize B)
  | eAbs A e => 1 + (esize A) + (esize e)
  | eApp e1 e2 => 1 + (esize e1) + (esize e2)
  | eLet e1 e2 => 1 + (esize e1) + (esize e2)
  | eSig A B => 1 + (esize A) + (esize B)
  | ePair e1 e2 A => 1 + (esize e1) + (esize e2) + (esize A)
  | eFst e => 1 + (esize e)
  | eSnd e => 1 + (esize e)
  | eIf e e1 e2 => 1 + (esize e) + (esize e1) + (esize e2) 
  | eTru => 1
  | eFls => 1
  | eBool => 1
end.

(*=============================
========Induction principle====
===============================*)

Inductive Vclosed : @term 0 -> Set :=
  | vc_eId (X: @atom 0) : Vclosed (eId X)
  | vc_eUni (U: universe) : Vclosed (eUni U)
  | vc_ePi (A: exp) (B: @exp 1) : Vclosed A -> (forall x, Vclosed (open x B)) -> Vclosed (ePi A B)
  | vc_eAbs (A: exp) (B: @exp 1) : Vclosed A -> (forall x, Vclosed (open x B)) -> Vclosed (eAbs A B)
  | vc_eSig (A: exp) (B: @exp 1) : Vclosed A -> (forall x, Vclosed (open x B)) -> Vclosed (eSig A B)
  | vc_ePair (v1 v2: exp) (A: exp) : Vclosed v1 -> Vclosed v2 -> Vclosed A -> Vclosed (ePair v1 v2 A)
  | vc_eTru : Vclosed (eTru)
  | vc_eFls : Vclosed (eFls)
  | vc_eBool: Vclosed (eBool)
  | vc_eLet (A: exp) (B: @exp 1) : Vclosed A -> (forall n, Vclosed (open n B)) -> Vclosed (eLet A B)
  | vc_eIf (v: exp) (e1 e2: exp) : Vclosed v -> Vclosed e1 -> Vclosed e2 -> Vclosed (eIf v e1 e2)
  | vc_eApp (v1 v2: exp) : Vclosed v1 -> Vclosed v2 -> Vclosed (eApp v1 v2)
  | vc_eFst (v: exp) : Vclosed v -> Vclosed (eFst v)
  | vc_eSnd (v: exp) : Vclosed v -> Vclosed (eSnd v).

Check Vclosed_ind.

Fixpoint Vclosedk (V : nat) : @term V -> Set :=
  match V with
  | 0 => fun t => Vclosed t
  | S V => fun t => forall n, Vclosedk V (open n t)
  end.

Fixpoint always_Vclosedk {V : nat} (t : term) {struct t} : Vclosedk V t :=
  match t with
  | eId x => 
    let fix go {V} : forall (x : @atom V), Vclosedk V (eId x) :=
      match V with 
      | 0 => vc_eId
      | S V => fun v n => go _ 
      end 
    in go x
  | eUni U =>
    let fix go {V} : forall (U : universe), Vclosedk V (eUni U) :=
      match V with 
      | 0 => vc_eUni
      | S V => fun v n => go _ 
      end 
    in go U
  | ePi A B => 
    let fix go {V} : forall A B, Vclosedk (V) A -> 
                      Vclosedk (S V) B -> 
                      Vclosedk V (ePi A B) :=
      match V with 
      | 0 => vc_ePi 
      | S V => fun _ _ vca vcb a=> go _ _ (vca a) (vcb a)
      end 
    in go _ _ (always_Vclosedk A) (always_Vclosedk B)
  | eAbs A B =>
    let fix go {V} : forall A B, Vclosedk (V) A -> 
                      Vclosedk (S V) B -> 
                      Vclosedk V (eAbs A B) :=
      match V with 
      | 0 => vc_eAbs 
      | S V => fun _ _ vca vcb a=> go _ _ (vca a) (vcb a)
      end 
    in go _ _ (always_Vclosedk A) (always_Vclosedk B)
  | eSig A B =>
    let fix go {V} : forall A B, Vclosedk (V) A -> 
                      Vclosedk (S V) B -> 
                      Vclosedk V (eSig A B) :=
      match V with 
      | 0 => vc_eSig 
      | S V => fun _ _ vca vcb a=> go _ _ (vca a) (vcb a)
      end 
    in go _ _ (always_Vclosedk A) (always_Vclosedk B)
  | ePair v1 v2 A =>
    let fix go {V} : forall v e1 e2, Vclosedk V v -> 
                                     Vclosedk V e1 ->
                                     Vclosedk V e2 ->
                                     Vclosedk V (ePair v e1 e2) :=
      match V with 
      | 0 => vc_ePair 
      | S V => fun _ _ _ vv1 vv2 va a => go _ _ _ (vv1 a) (vv2 a) (va a) 
      end 
    in go _ _ _ (always_Vclosedk v1) (always_Vclosedk v2) (always_Vclosedk A)
  | eTru =>
    let fix go {V} : Vclosedk V _ :=
      match V with 0 => vc_eTru | S V => fun _ => go end in
    go
  | eFls =>
    let fix go {V} : Vclosedk V _ :=
      match V with 0 => vc_eFls | S V => fun _ => go end in
    go
  | eBool =>
    let fix go {V} : Vclosedk V _ :=
      match V with 0 => vc_eBool | S V => fun _ => go end in
    go
  | eLet A B =>
    let fix go {V} : forall A B, Vclosedk (V) A -> 
                      Vclosedk (S V) B -> 
                      Vclosedk V (eLet A B) :=
      match V with 
      | 0 => vc_eLet 
      | S V => fun _ _ vca vcb a=> go _ _ (vca a) (vcb a)
      end 
    in go _ _ (always_Vclosedk A) (always_Vclosedk B)
  | eIf v e1 e2 => 
    let fix go {V} : forall v e1 e2, Vclosedk V v -> 
                                     Vclosedk V e1 ->
                                     Vclosedk V e2 ->
                                     Vclosedk V (eIf v e1 e2) :=
      match V with 
      | 0 => vc_eIf 
      | S V => fun _ _ _ vv ve1 ve2 a => go _ _ _ (vv a) (ve1 a) (ve2 a) 
      end 
    in go _ _ _ (always_Vclosedk v) (always_Vclosedk e1) (always_Vclosedk e2)
  | eApp f e  =>
    let fix go {V} : forall f e, Vclosedk V f -> 
                                 Vclosedk V e -> 
                                 Vclosedk V (eApp f e) :=
      match V with 
      | 0 => vc_eApp 
      | S V => fun _ _ vf ve a => go _ _ (vf a) (ve a) 
      end 
    in go _ _ (always_Vclosedk f) (always_Vclosedk e)
  | eFst v =>
    let fix go {V} : forall v, Vclosedk V v -> 
                                 Vclosedk V (eFst v) :=
      match V with 
      | 0 => vc_eFst 
      | S V => fun _ vv a => go _ (vv a) 
      end 
    in go _ (always_Vclosedk v)
  | eSnd v =>
    let fix go {V} : forall v, Vclosedk V v -> 
                                 Vclosedk V (eSnd v) :=
      match V with 
      | 0 => vc_eSnd 
      | S V => fun _ vv a => go _ (vv a) 
      end 
    in go _ (always_Vclosedk v)
end.

(* Lemma always_Vclosedk_open x : forall {V} (t : @term (1 + V)),
  always_Vclosedk t x = always_Vclosedk (open x t).
Proof.
  intros.
  inductT t; induction V0; cbn; try easy.
  - rewrite IHt; easy.
  - rewrite IHt; easy.
  - rewrite IHt1, IHt2; try apply heq_intro; easy.
  - rewrite IHt1, IHt2; try apply heq_intro; easy.
Qed.
Hint Rewrite always_Vclosedk_open : rw_names. *)

Check Vclosed_ind.

Definition term_ind
             (P : @exp 0 -> Prop)
             (IDD : forall (v : atom), P (eId v))
             (UNI : forall (U : universe), P (eUni U))
             (TRU : P (eTru))
             (FLS : P (eFls))
             (BOO : P (eBool))
             (ABS : forall (A B : exp),
                 P (A) ->
                 (forall (n : name), P (open n B)) ->
                 P (eAbs A B))
             (PIE : forall (A B : exp),
                 P (A) ->
                 (forall (n : name), P (open n B)) ->
                 P (ePi A B))
             (SIG : forall (A B : exp),
                 P (A) ->
                 (forall (n : name), P (open n B)) ->
                 P (eSig A B))
             (LET : forall (A B : exp),
                 P (A) ->
                 (forall (n : name), P (open n B)) ->
                 P (eLet A B))
             (APP : forall (f e : exp), P f -> P e -> P (eApp f e))
             (PAI : forall (v1 v2 A : exp), P v1 -> P v2 -> P A -> P (ePair v1 v2 A))
             (IFF : forall (v e1 e2 : exp), P v -> P e1 -> P e2 -> P (eIf v e1 e2))
             (FST : forall (v : exp), P v -> P (eFst v))
             (SND : forall (v : exp), P v -> P (eSnd v))
             (tm : exp) : P tm :=
    Vclosed_ind (fun tm _ => P tm)
       IDD UNI 
       (fun a b _ Ha _ Hb => PIE a b Ha Hb)
       (fun a b _ Ha _ Hb => ABS a b Ha Hb)
       (fun a b _ Ha _ Hb => SIG a b Ha Hb)
       (fun v1 v2 a _ Hv1 _ Hv2 _ Ha => PAI v1 v2 a Hv1 Hv2 Ha) 
       TRU FLS BOO 
       (fun a b _ Ha _ Hb => LET a b Ha Hb) 
       (fun v e1 e2 _ Hv _ He1 _ He2 => IFF v e1 e2 Hv He1 He2) 
       (fun f e _ F _ E => APP f e F E) 
       (fun v _ V => FST v V)
       (fun v _ V => SND v V)
       tm (always_Vclosedk tm).

Check Vclosed_ind.


(* 
============================================================
=======--ANF Syntactic Restriction--======================== 
============================================================

Which terms are ANF? We have a judgment for it.
*)

Inductive isConf: @exp 0 -> Prop :=
| CompIs (c: exp):
  isComp c -> isConf c
| Let (A: exp) (B: exp):
  isComp A ->
  (forall x, isConf (open x B)) ->
  isConf (eLet A B)
| If (v: exp) (e1 e2: exp):
  isVal v ->
  isConf e1 ->
  isConf e2 ->
  isConf (eIf v e1 e2)
with isComp: exp -> Prop :=
| ValIs (v: exp) :
  isVal v -> isComp v
| Fst (v: exp):
  isVal v -> 
  isComp (eFst v)
| Snd (v: exp):
  isVal v -> 
  isComp (eSnd v)
| App (v1 v2: exp):
  isVal v1 ->
  isVal v2 -> 
  isComp (eApp v1 v2)
with isVal: exp -> Prop :=
| Id (x: atom):
  isVal (eId x)
| Tru:
  isVal (eTru)
| Fls:
  isVal (eFls)
| Bool:
  isVal (eBool)
| Uni (U: universe):
  isVal (eUni U)
| Pair (v1 v2: exp) (A: exp):
  isVal v1 ->
  isVal v2 ->
  isConf A ->
  isVal (ePair v1 v2 A)
| Pi (A: exp) (B: exp):
  isConf A ->  
  (forall x, isConf (open x B)) ->
  isVal (ePi A B)
| Abs (A: exp) (B: exp):
  isConf A ->  
  (forall x, isConf (open x B)) ->
  isVal (eAbs A B)
| Sig (A: exp) (B: exp):
  isConf A ->  
  (forall x, isConf (open x B)) ->
  isVal (eSig A B)
.
Hint Constructors isConf isVal isComp.
Check Let.

Definition Conf:= {e: exp | isConf e}.
Definition Comp:= {e: exp | isComp e}.
Definition Val:= {e: exp | isVal e}.


Scheme val_conf_mut := Induction for isVal Sort Prop
with conf_comp_mut := Induction for isConf Sort Prop
with comp_val_mut := Induction for isComp Sort Prop.

Combined Scheme val_conf_comp_comb from val_conf_mut, conf_comp_mut, comp_val_mut.

Check val_conf_comp_comb.


Definition reprove_conf (e: exp) (P: isConf e) (r: ren) (t: total r) :  isConf ([r] e). Admitted.


Fixpoint reprove_val (e: exp) (P: isVal e) (r: ren) (t: total r) :  isVal ([r] e):=
match P with
| Id x => Id (applyt r t x)
| Pair v1 v2 A Pv1 Pv2 PA =>
  Pair (reprove_val v1 _ r t) (reprove_val v2 _ r t) (reprove_conf A _ r t)
end.
| Pi (A: exp) (B: exp):
  isConf A ->  
  (forall x, isConf (open x B)) ->
  isVal (ePi A B)
| Abs (A: exp) (B: exp):
  isConf A ->  
  (forall x, isConf (open x B)) ->
  isVal (eAbs A B)
| Sig (A: exp) (B: exp):
  isConf A ->  
  (forall x, isConf (open x B)) ->
  isVal (eSig A B)

Lemma weakening2:
forall (e: exp),
(isVal e  -> (forall r,
total r -> isVal ([r] e))) /\
(isConf e  -> (forall r,
total r -> isConf ([r] e))) /\
(isComp e  -> (forall r,
total r ->isComp ([r] e))).
Proof.


Lemma weakening2:
forall r,
total r ->

  (forall (e: exp), isVal e  -> isVal ([r] e))
  /\
  (forall (e: exp), isConf e  -> isConf ([r] e))
  /\
  (forall (e: exp), isComp e  -> isComp ([r] e)).
Proof.

Qed.

Lemma weakening2:
forall (e: exp),
(isVal e  -> (forall r,
total r -> isVal ([r] e))) /\
(isConf e  -> (forall r,
total r -> isConf ([r] e))) /\
(isComp e  -> (forall r,
total r ->isComp ([r] e))).
Proof.
intros. induction e using term_ind.
+ repeat split; induction r.
  - intros. names. auto.
  - intros. names. apply IHr1. apply Id. 
+ names. auto.
+  shelve.
+ split. apply IHr. apply val_conf_comp_comb; intros; names; auto.
+ induction e. apply val_conf_comp_comb; try (intros; names; auto; fail).
  - intros. destruct H. cbn. apply IHr1; auto. destruct IHr2; auto. apply H1 with (e:= eId x). apply Id.
  - intros. cbn. constructor; auto. apply H1.
+ intros. names. auto.
  - induction 1; cbn; intros * rl; eauto.
  - rewrite applyt_related with (rl := rl).
    auto with contexts.
  - constructor; intro.
    names; auto with contexts.
+ cbn in H. contradiction.
Qed.
(* Lemma ANF_nominal_irrelevance:
, forall (e: exp),
(isVal e -> forall (x y: name), isVal (open y (close x e)))
/\
(isConf e -> forall (x y: name), isConf (open y (close x e)))
/\
(isComp e -> forall (x y: name), isComp (open y (close x e))).
Proof. intros. cbn.   

induction e using term_ind.
all: try (cbn; repeat split; auto ; fail).
+ cbn; repeat split. intros. 
  - inversion H0. apply Abs with (x:=x).
    * apply IHe1. auto.
    * names. apply IHe1. auto.


apply val_conf_comp_comb; try (cbn; constructor; auto; fail). 
+ intros. names in H. names in H0. names. apply Pi. ; auto.

Lemma ANF_nominal_irrelevance:
forall (x y: name),
forall (e: exp),
(isVal e -> forall (x y: name), isVal (open y (close x e)))
/\
(isConf e -> forall (x y: name), isConf (open y (close x e)))
/\
(isComp e -> forall (x y: name), isComp (open y (close x e)))
.
Proof. intros.  
induction e using term_ind.
all: try (cbn; repeat split; auto ; fail).
+ cbn; repeat split. intros. 
  - inversion H0. destruct H with (n:=x). destruct H4. *)

(* 
=====================================
=======--Type Environments--=========
=====================================
*)

Inductive ctxmem :=
| Assum (A: @exp 0)
| Def (e: @exp 0) (A: @exp 0)
| Eq (e1: @exp 0) (e2: @exp 0) 
.

Definition env := @context ctxmem.

Inductive assumes (g: env) (x: atom) (A: exp) :=
| ass :
  (has g x (Assum A)) ->
  assumes g x A
| def (e: @exp 0):
  (has g x (Def e A)) ->
  assumes g x A
.

Hint Constructors assumes.

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
| g'' & x ~ A => ((append g'' g') & x ~ A)
end. 

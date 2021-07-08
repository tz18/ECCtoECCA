Require Export Atom.
Require Import String Morph Var Context Relative.
Require Import Coq.Program.Wf.
Require Import FunInd.
Require Import Recdef.
Require Import Lia. 
Require Import JMeq.
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
  | eRefl (v: exp)
  | eEqv (v1 v2: exp)
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
      | eRefl e => eRefl (kleisli f V e)
      | eEqv e1 e2 => eEqv (kleisli f V e1) (kleisli f V e2)
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
  | eRefl e => 1 + esize e
  | eEqv e1 e2 => 1 + esize e1 + esize e2  
end.

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
  | vc_eSnd (v: exp) : Vclosed v -> Vclosed (eSnd v)
  | vc_eRefl (v: exp): Vclosed v -> Vclosed (eRefl v)
  | vc_eEqv (v1: exp) (v2: exp): Vclosed v1 -> Vclosed v2 -> Vclosed (eEqv v1 v2)
.

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
  | eRefl v =>
    let fix go {V} : forall v, Vclosedk V v ->
                                 Vclosedk V (eRefl v) :=
      match V with
      | 0 => vc_eRefl
      | S V => fun _ vv a => go _ (vv a)
      end
    in go _ (always_Vclosedk v)
  | eEqv f e  =>
    let fix go {V} : forall f e, Vclosedk V f ->
                                 Vclosedk V e ->
                                 Vclosedk V (eEqv f e) :=
      match V with
      | 0 => vc_eEqv
      | S V => fun _ _ vf ve a => go _ _ (vf a) (ve a)
      end
    in go _ _ (always_Vclosedk f) (always_Vclosedk e)
end.

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
             (RFL : forall (v : exp), P v -> P (eRefl v))
             (EQV : forall (e1 e2 : exp), P e1 -> P e2 -> P (eEqv e1 e2))
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
       (fun v _ V => RFL v V)
       (fun e1 e2 _ E1 _ E2 => EQV e1 e2 E1 E2)
       tm (always_Vclosedk tm).

(*
============================================================
=======--ANF Syntactic Restriction--========================
============================================================

Which terms are ANF? We have a judgment for it.
*)

Inductive isConf {V}: @exp V -> Prop :=
| Let (A: exp) (B: exp):
  isComp A ->
  isConf B ->
  isConf (eLet A B)
| If (v: exp) (e1 e2: exp):
  isVal v ->
  isConf e1 ->
  isConf e2 ->
  isConf (eIf v e1 e2)
| CompIs (c: exp):
  isComp c -> isConf c
with isComp {V}: exp -> Prop :=
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
| ValIs (v: exp) :
  isVal v -> isComp v
with isVal {V}: exp -> Prop :=
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
  isConf B ->
  isVal (ePi A B)
| Abs (A: exp) (B: exp):
  isConf A ->
  isConf B ->
  isVal (eAbs A B)
| Sig (A: exp) (B: exp):
  isConf A ->
  isConf B ->
  isVal (eSig A B)
| Refl (v: exp):
  isVal v ->
  isVal (eRefl v)
| Eqv (v1 v2: exp):
  isVal v1 ->
  isVal v2 ->
  isVal (eEqv v1 v2)
.
Hint Constructors isConf isVal isComp.

Scheme val_conf_mut := Induction for isVal Sort Prop
with conf_comp_mut := Induction for isConf Sort Prop
with comp_val_mut := Induction for isComp Sort Prop.

Combined Scheme val_conf_comp_comb from val_conf_mut, conf_comp_mut, comp_val_mut.

(*"Structure equivalent" same tree of constructors*)
Inductive squiv {V V1} : @exp V -> @exp V1 -> Prop:=
  | squivId (x: atom) (y: atom):
    squiv (eId x) (eId y)
  | squivUni (U U': universe):
    squiv (eUni U) (eUni U')
  | squivPi (A: exp) (A': exp) (B: exp) (B': exp):
    squiv A A' ->
    squiv B B' ->
    squiv (ePi A B) (ePi A' B')
  | squivAbs (A: exp) (A': exp) (B: exp) (B': exp):
    squiv A A' ->
    squiv B B' ->
    squiv (eAbs A B) (eAbs A' B')
  | squivSig (A: exp) (A': exp) (B: exp) (B': exp):
    squiv A A' ->
    squiv B B' ->
    squiv (eSig A B) (eSig A' B')
  | squivPair (v1 v1' v2 v2' A A': exp):
    squiv v1 v1' ->
    squiv v2 v2' ->
    squiv A A' ->
    squiv (ePair v1 v2 A) (ePair v1' v2' A')
  | squivTru:
    squiv eTru eTru
  | squivFls:
    squiv eFls eFls
  | squivBool:
    squiv eBool eBool
  | squivLet (A: exp) (A': exp) (B: exp) (B': exp):
    squiv A A' ->
    squiv B B' ->
    squiv (eLet A B) (eLet A' B')
  | squivIf (v v': exp) (e1 e1' e2 e2': exp):
    squiv v v' ->
    squiv e1 e1' ->
    squiv e2 e2' ->
    squiv (eIf v e1 e2) (eIf v' e1' e2')
  | squivApp (v1 v2 v1' v2': exp):
    squiv v1 v1' ->
    squiv v2 v2' ->
    squiv (eApp v1 v2) (eApp v1' v2')
  | squivFst (v v': exp):
    squiv v v' ->
    squiv (eFst v) (eFst v')
  | squivSnd (v v': exp):
    squiv v v' ->
    squiv (eSnd v) (eSnd v')
  | squivRefl (v v': exp):
    squiv v v' ->
    squiv (eRefl v) (eRefl v')
  | squivEqv (v1 v1' v2 v2': exp):
    squiv v1 v1' ->
    squiv v2 v2' ->
    squiv (eEqv v1 v2) (eEqv v1' v2')
.
Hint Constructors squiv.

Fixpoint propOpen (p: @term 0 -> Prop) (V : nat): @term V -> Prop :=
  match V with
  | 0 => fun t => (p t)
  | S V => fun t => forall n, propOpen p V (open n t)
  end.
Definition isConfk:= propOpen (@isConf 0).
Definition isCompk:= propOpen (@isComp 0).
Definition isValk:= propOpen (@isVal 0).


(*
================================
========== Naming lemmas ===============
================================
*)

Lemma renamings_rename (r: ren) (t: total r): 
forall  {V} x, exists y, ([r] @eId V x) = eId y.
Proof.
induction r.
+ names. eauto.
+ names. names in IHr1. names in IHr2. intros. destruct IHr2 with (x:= x). apply t.
rewrite H. names. destruct IHr1 with V x0. apply t. eauto.
+ intros. names. destruct IHr with V x. apply t. names in H. rewrite H. names. eauto.
+ intros. names. destruct IHr with (S V) (closev a x). apply t. names in H. rewrite H. names. eauto.
+ contradiction.
Qed.

Lemma renaming_ids_pANF: forall {V} (r: ren) (t: total r) x, @isVal V ([r] (eId x)).
Proof.
intros. cbn in *. destruct renamings_rename with r V x. auto. cbn in *. rewrite H. apply Id.
Qed.

Hint Resolve renamings_rename.
Hint Resolve renaming_ids_pANF.


Lemma squiv_sym {V V1} (e: @exp V) (e': @exp V1):
squiv e e' -> squiv e' e.
Proof.
intros; induction H; auto. Qed.
Hint Resolve squiv_sym.

Definition structure_preserving {V1} {V2} (f: (@exp V1 -> @exp V2)): Prop :=
forall (e: exp),
squiv (f e) e.

Lemma total_renamings_preserve_structure:
forall {V} (e: @exp V) (r: ren) (t: total r), squiv ([r]e) e.
Proof. intros.
induction e.
all: try  (cbn; auto; fail).
+ cut (exists y, ([r] @eId V x) = eId y). 
  - intros. destruct H. rewrite H. apply squivId.
  - auto.
Qed.

Lemma name_operations_preserve_structure {V}:
(forall (x: name), structure_preserving (@open x V)) /\
(forall (x: name), structure_preserving (@close x V)) /\
(structure_preserving (@wk V)).
Proof.
intros.
unfold structure_preserving. repeat split. all: intros; inductT e; try (constructor; fail).
all: try (constructor;
  (try (apply IHe1; simpl_term_eq; auto; fail));
  (try (apply IHe2; simpl_term_eq; auto); fail); fail).
all: try (constructor; apply IHe; simpl_term_eq; auto; fail).
all: constructor.
1,4,7,10,13,16: apply IHe1 ; simpl_term_eq; auto.
1,3,5,7,9,11: apply IHe2 ; simpl_term_eq; auto.
all: apply IHe3; simpl_term_eq; auto.
Qed.
Hint Resolve name_operations_preserve_structure.

Lemma open_preserves_structure {V}:
forall (x: name), structure_preserving (@open x V).
Proof.
apply name_operations_preserve_structure.
Qed.
Hint Resolve open_preserves_structure.

Lemma close_preserves_structure {V}:
forall (x: name), structure_preserving (@close x V).
Proof. 
apply name_operations_preserve_structure.
Qed.
Hint Resolve close_preserves_structure.

Lemma wk_preserves_structure {V}:
structure_preserving (@wk V).
Proof.
apply name_operations_preserve_structure.
Qed.
Hint Resolve close_preserves_structure.

Ltac invertANFhelper e:=
  match goal with
    | [ H : isConf ( e ) |- _ ] => inversion H; clear H; subst
    | [ H : isComp ( e ) |- _ ] => inversion H; clear H; subst
    | [ H: isVal ( e ) |- _ ] => inversion H; clear H; subst
  end.

Ltac invertANF:=
  match goal with
    | [ H : isConf ( ?e ) |- _ ] => repeat invertANFhelper e
    | [ H : isComp ( ?e ) |- _ ] => repeat invertANFhelper e
    | [ H: isVal ( ?e ) |- _ ] => repeat invertANFhelper e
  end.

Ltac destructConj:=
  match goal with
    | [ H : ( _ /\ _ ) |- _ ] => destruct H
  end.

Ltac constructANFhelper e :=
  match goal with
    | [ |- isConf e ] => constructor
    | [ |- isComp e ] => constructor
    | [ |- isVal e ] => constructor
  end.

Ltac constructANF:=
  match goal with
    | [ |- isConf ?e ] => repeat constructANFhelper e
    | [ |- isComp ?e ] => repeat constructANFhelper e
    | [ |- isVal ?e ] => repeat constructANFhelper e
  end.

Lemma squiv_proper_over_ANF:
forall {V} {V'} (e: @exp V) (e': @exp V'), squiv e e' ->
((@isConf V e -> @isConf V' e')
/\ (@isComp V e -> @isComp V' e')
/\ (@isVal V e -> @isVal V' e')).
Proof.
intros. induction H; auto.
1-4,10,11:repeat split; repeat destructConj; intros; constructANF; invertANF; auto.
1,2: repeat split; repeat destructConj; intros; try apply Let; invertANF; auto.
+ repeat split; repeat destructConj; intros. constructor; apply App; invertANF; auto.
  - apply App; invertANF; auto.
  - invertANF.
+ repeat split; repeat destructConj; intros. constructor; apply Fst; invertANF; auto.
  - apply Fst; invertANF; auto.
  - invertANF.
+ repeat split; repeat destructConj; intros. constructor; apply Snd; invertANF; auto.
  - apply Snd; invertANF; auto.
  - invertANF.
Qed.
Hint Resolve squiv_proper_over_ANF.

Lemma total_renamings_preserve_ANF :
forall r,
total r ->
let P (V: nat) (e: @exp V) (i: isVal e):= isVal ([r] e) in
let P0 (V: nat) (e: @exp V) (i: isConf e):= isConf ([r] e) in
let P1 (V: nat) (e: @exp V) (i: isComp e):= isComp ([r] e) in
forall (V: nat),
  (forall (e: @exp V) (i: isVal e), P V e i)
  /\
  (forall (e: @exp V) (i: isConf e), P0 V e i)
  /\
  (forall (e: @exp V) (i: isComp e), P1 V e i).
Proof.
intros. cbn. apply val_conf_comp_comb; intros; unfold P in *; unfold P0 in *; unfold P1 in *.
2,3,4,5: constructor.
2,3,4,5,6,7,9,10,11,12,13: cbn; constructor; auto.
2,3: cbn; constructor; auto.
apply renaming_ids_pANF. auto.
Qed.
Hint Resolve total_renamings_preserve_ANF.
Check val_conf_comp_comb.

Lemma open_is_renaming:
forall (x y: name),
forall (V: nat) (e: @exp (S V)), open y e = [y <- x] (open x e).
Proof.
intros; names; auto.
Qed.
Hint Rewrite open_is_renaming.

Lemma ANF_by_any_other_name:
forall (x y: name),
forall (V: nat),
  (forall (e: @exp (S V)) (i: isVal (open x e)),  isVal (open y e))
  /\
  (forall (e: @exp (S V)) (i: isConf (open x e)), isConf (open y e))
  /\
  (forall (e: @exp (S V)) (i: isComp (open x e)), isComp (open y e)).
Proof.
intros. names. repeat split; intros;
rewrite open_is_renaming with (e:=e) (x:=x); apply total_renamings_preserve_ANF;
     cbn; auto.
Qed.
Hint Resolve ANF_by_any_other_name.

Lemma struct_preserving_ANF_iff {V1}{V2}:
forall (f: (@exp V1 -> @exp V2)) (h: structure_preserving f),
  (forall (e: @exp (V1)), isVal (f e) <->  isVal e)
  /\
  (forall (e: @exp (V1)), isConf (f e)<-> isConf e)
  /\
  (forall (e: @exp (V1)), isComp (f e)<-> isComp e).
Proof.
intros. repeat split.
all: try (intros; unfold structure_preserving in h; pose (@squiv_proper_over_ANF V1); apply a with (e':=(f e)) (e:=e); auto).
all: try (intros; unfold structure_preserving in h; pose (@squiv_proper_over_ANF V2); apply a with (e:=(f e)) (e':=e); auto).
Qed.

Lemma open_ANF_iff:
forall (x: name),
forall {V},
  (forall (e: @exp (S V)), isVal (open x e) <->  isVal e)
  /\
  (forall (e: @exp (S V)), isConf (open x e)<-> isConf e)
  /\
  (forall (e: @exp (S V)), isComp (open x e)<-> isComp e).
Proof. intros. apply struct_preserving_ANF_iff with (f:= (open x)).
apply open_preserves_structure.
Qed.
Hint Resolve open_ANF_iff.

Lemma open_conf {V} {x: name} {e: @exp (S V)}: @isConf (S V) e -> (isConf (open x e)).
Proof. apply open_ANF_iff. Qed.
Hint Resolve open_conf.
Lemma unopen_conf {V} {x: name} {e: @exp (S V)}: isConf (open x e) -> (@isConf (S V) e).
Proof. apply open_ANF_iff with (x:=x). Qed.
Hint Resolve unopen_conf.

Lemma close_ANF_iff:
forall (x: name),
forall {V},
  (forall (e: @exp V), isVal (close x e) <-> isVal e)
  /\
  (forall (e: @exp V), isConf (close x e) <-> isConf e)
  /\
  (forall (e: @exp V), isComp (close x e) <-> isComp e).
Proof.
intros. apply struct_preserving_ANF_iff with (f:=(close x)). apply close_preserves_structure.
Qed.

Lemma wk_ANF_iff:
forall {V},
  (forall (e: @exp V), isVal (wk e) <-> isVal e)
  /\
  (forall (e: @exp V), isConf (wk e) <-> isConf e)
  /\
  (forall (e: @exp V), isComp (wk e) <-> isComp e).
Proof.
intros. apply struct_preserving_ANF_iff with (f:=(wk)). apply wk_preserves_structure.
Qed.

Lemma wk_conf {V} {e: @exp V}: @isConf V e -> (isConf (wk e)).
Proof. apply wk_ANF_iff. Qed.
Hint Resolve wk_conf.

Lemma shift_conf {V} {x: name} {e: @exp V}:
isConf e -> isConf ([^ x] e).
Proof.
rewrite <- rw_group_shift. intros. auto.
Qed.

(* Induction principle on ANF judgment *)

Section ANF_val_conf_comp_comb.

Variables
(P :  forall (e : @exp 0), isVal e -> Prop)
(P0 : forall (e : @exp 0), isConf e -> Prop)
(P1 : forall (e : @exp 0), isComp e -> Prop).
Let fIdT:= (forall (x : atom), P (eId x) (Id x)).
Let fTruT:= (P eTru Tru).
Let fFlsT:= (P eFls Fls).
Let fBoolT:= (P eBool Bool).
Let fUniT:= (forall (U : universe), P (eUni U) (Uni U)).
Let fPairT:= (forall (v1 v2 A : exp) (i : isVal v1),
        P v1 i ->
        forall (i0 : isVal v2),
        P v2 i0 ->
        forall (i1 : isConf A),
        P0 A i1 ->
        P (ePair v1 v2 A) (Pair v1 v2 A i i0 i1)).
Let fPiT:= (forall (A: exp) (B : @exp (S 0)) (i : isConf A),
        P0 A i ->
        forall (i0 : isConf B),
        (forall (x : name),
        P0 (open x B) (open_conf i0)) ->
        P (ePi A B) (Pi A B i i0)).
Let fAbsT:= (forall (A: exp) (B : @exp (S 0)) (i : isConf A),
        P0 A i ->
        forall (i0 : isConf B),
        (forall (x : name),
        P0 (open x B) (open_conf i0)) ->
        P (eAbs A B) (Abs A B i i0)).
Let fSigT:= (forall (A: exp) (B : @exp (S 0)) (i : isConf A),
        P0 A i ->
        forall (i0 : isConf B),
        (forall (x : name),
        P0 (open x B) (open_conf i0)) ->
        P (eSig A B) (Sig A B i i0)).
Let fLetT:= (forall (A: exp) (B : @exp (S 0)) (i : isComp A),
        P1 A i ->
        forall (i0 : isConf B),
        (forall (x : name),
        P0 (open x B) (open_conf i0)) ->
        P0 (eLet A B) (Let A B i i0)).
Let fIfT:= (forall (v e1 e2 : exp)
          (i : isVal v),
        P v i ->
        forall (i0 : isConf e1),
        P0 e1 i0 ->
        forall (i1 : isConf e2),
        P0 e2 i1 ->
        P0 (eIf v e1 e2) (If v e1 e2 i i0 i1)).
Let fCompT:= (forall (c : exp) (i : isComp c),
        P1 c i -> P0 c (CompIs c i)).
Let fFstT:=  (forall (v : exp) (i : isVal v),
        P v i -> P1 (eFst v) (Fst v i)).

Let fSndT:= (forall (v : exp) (i : isVal v),
        P v i -> P1 (eSnd v) (Snd v i)).

Let fAppT:=  (forall (v1 v2 : exp)
          (i : isVal v1),
        P v1 i ->
        forall (i0 : isVal v2),
        P v2 i0 ->
        P1 (eApp v1 v2) (App v1 v2 i i0)).
Let fValT:= (forall (v : exp) (i : isVal v),
        P v i -> P1 v (ValIs v i)).
Let fRflT:= (forall (v: exp) (i: isVal v),
    P v i -> P (eRefl v) (Refl v i)).
Let fEqvT:=  (forall (v1 v2 : exp)
          (i : isVal v1),
        P v1 i ->
        forall (i0 : isVal v2),
        P v2 i0 ->
        P (eEqv v1 v2) (Eqv v1 v2 i i0)).

Variable (fId: fIdT) (fTru: fTruT) (fFls: fFlsT) (fBool: fBoolT) (fUni: fUniT) (fPair: fPairT) (fPi: fPiT) (fAbs: fAbsT) (fSig: fSigT)
        (fLet: fLetT) (fIf: fIfT) (fComp: fCompT)
        (fFst: fFstT) (fSnd: fSndT) (fApp: fAppT) (fVal: fValT)
        (fRfl: fRflT) (fEqv: fEqvT).

Definition ANF_val_conf_comp_comb_type
     :=
       (forall (e : @exp 0) (i : isVal e), P e i) /\
       (forall (e : @exp 0) (i : isConf e), P0 e i) /\
       (forall (e : @exp 0) (i : isComp e), P1 e i).

Definition isANF {V} (e : @exp V) : Type := (isVal e) + ((isConf e) + (isComp e)).

Definition anfP (e : exp) (i : isANF e) :=
  match i with
  | inl i => P e i
  | inr (inl i) => P0 e i
  | inr (inr i) => P1 e i
  end.

Program Fixpoint FANF (e : @exp 0) (g: isANF e) {measure (esize e)}: anfP e g :=
  match g with
    | inl ib =>
      match ib with
      | Id x => fId x
      | Tru => fTru
      | Fls => fFls
      | Bool => fBool
      | Uni U => fUni U
      | Pair v1 v2 A i1 i2 i3 => (fPair v1 v2 A i1 (FANF v1 (inl i1)) i2 (FANF v2 (inl i2)) i3 (FANF A (inr (inl i3))))
      | Pi A B iA iB => (fPi A B
                        iA (FANF A (inr (inl iA)))
                        iB (fun x => (FANF (open x B) (inr (inl (open_conf iB))))))
      | Abs A B iA iB => (fAbs A B
                               iA (FANF A (inr (inl iA)))
                               iB (fun x => (FANF (open x B) (inr (inl (open_conf iB))))))
      | Sig A B iA iB => (fSig A B
                               iA (FANF A (inr (inl iA)))
                               iB (fun x => (FANF (open x B) (inr (inl (open_conf iB))))))
      | Refl v i => (fRfl v i (FANF v (inl i)))
      | Eqv v1 v2 i1 i2 => (fEqv v1 v2 i1 (FANF v1 (inl i1)) i2 (FANF v2 (inl i2)))
      end
    | inr (inl ic) =>
      match ic with
      | Let A B iA iB => (fLet A B
                        iA (FANF A (inr (inr iA)))
                        iB (fun x => (FANF (open x B) (inr (inl (open_conf iB))))))
      | If v e1 e2 iV iE1 iE2 => (fIf v e1 e2
                                      iV (FANF v (inl iV))
                                      iE1 (FANF e1 (inr (inl iE1)))
                                      iE2 (FANF e2 (inr (inl iE2))))
      | CompIs C iC => 
          (*(fComp C iC (FANF C (inr (inr iC))))*)
            (fComp C iC (
              match iC with
              | App v1 v2 iV1 iV2 => (fApp v1 v2
                                           iV1 (FANF v1 (inl iV1))
                                           iV2 (FANF v2 (inl iV2)))
              | Fst v iV => (fFst v iV (FANF v (inl iV)))
              | Snd v iV => (fSnd v iV (FANF v (inl iV)))
              | ValIs v iV => 
                  (*(fVal v iV (FANF v (inl iV)))*)
                  (fVal v iV (
                    match iV with
                      | Id x => fId x
                      | Tru => fTru
                      | Fls => fFls
                      | Bool => fBool
                      | Uni U => fUni U
                      | Pair v1 v2 A i1 i2 i3 => (fPair v1 v2 A i1 (FANF v1 (inl i1)) i2 (FANF v2 (inl i2)) i3 (FANF A (inr (inl i3))))
                      | Pi A B iA iB => (fPi A B
                                        iA (FANF A (inr (inl iA)))
                                        iB (fun x => (FANF (open x B) (inr (inl (open_conf iB))))))
                      | Abs A B iA iB => (fAbs A B
                                               iA (FANF A (inr (inl iA)))
                                               iB (fun x => (FANF (open x B) (inr (inl (open_conf iB))))))
                      | Sig A B iA iB => (fSig A B
                                               iA (FANF A (inr (inl iA)))
                                               iB (fun x => (FANF (open x B) (inr (inl (open_conf iB))))))
                      | Refl v i => (fRfl v i (FANF v (inl i)))
                      | Eqv v1 v2 i1 i2 => (fEqv v1 v2 i1 (FANF v1 (inl i1)) i2 (FANF v2 (inl i2)))
                      end))
               end))
      end
    | inr (inr id) =>
      match id with
      | App v1 v2 iV1 iV2 => (fApp v1 v2
                                   iV1 (FANF v1 (inl iV1))
                                   iV2 (FANF v2 (inl iV2)))
      | Fst v iV => (fFst v iV (FANF v (inl iV)))
      | Snd v iV => (fSnd v iV (FANF v (inl iV)))
      | ValIs v iV => 
          (*fVal v iV (FANF v (inl iV)))*)
          (fVal v iV (
            match iV with
            | Id x => fId x
            | Tru => fTru
            | Fls => fFls
            | Bool => fBool
            | Uni U => fUni U
            | Pair v1 v2 A i1 i2 i3 => (fPair v1 v2 A i1 (FANF v1 (inl i1)) i2 (FANF v2 (inl i2)) i3 (FANF A (inr (inl i3))))
            | Pi A B iA iB => (fPi A B
                              iA (FANF A (inr (inl iA)))
                              iB (fun x => (FANF (open x B) (inr (inl (open_conf iB))))))
            | Abs A B iA iB => (fAbs A B
                                     iA (FANF A (inr (inl iA)))
                                     iB (fun x => (FANF (open x B) (inr (inl (open_conf iB))))))
            | Sig A B iA iB => (fSig A B
                                     iA (FANF A (inr (inl iA)))
                                     iB (fun x => (FANF (open x B) (inr (inl (open_conf iB))))))
            | Refl v i => (fRfl v i (FANF v (inl i)))
            | Eqv v1 v2 i1 i2 => (fEqv v1 v2 i1 (FANF v1 (inl i1)) i2 (FANF v2 (inl i2)))
            end))
      end
  end.
Show Obligation Tactic. Solve All Obligations with (Tactics.program_simpl; try rewrite esize_open_id; cbn; lia). 

Definition ANF_val_conf_comp_comb: ANF_val_conf_comp_comb_type := 
conj (fun (e : @exp 0) (i : isVal e) => FANF e (inl i))
 (conj (fun (e : @exp 0) (i : isConf e) => FANF e (inr (inl i))) (fun (e : @exp 0) (i : isComp e) => FANF e (inr (inr i))))
.

End ANF_val_conf_comp_comb.


(*
=====================================
=======--Type Environments--=========
=====================================
*)

Inductive ctxmem :=
| Assum (A: @exp 0)
| Def (e: @exp 0) (A: @exp 0).

Definition env := @context ctxmem.

Definition assumes (g: env) (x: atom) (A: exp) :=
(has g x (Assum A)) \/ (exists (e: exp), (has g x (Def e A))).
Hint Unfold assumes.

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

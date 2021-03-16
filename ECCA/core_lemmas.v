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

(*=============================
======Restricted Induction=====
===============================*)

Inductive Vclosed_val: @val 0 -> Set :=
  | vc_Id (x: @atom 0) : Vclosed_val (Id x)
  | vc_Uni (U: universe): Vclosed_val (Uni U)
  | vc_Pi (A: conf) (B: @conf 1): Vclosed_conf A -> (forall x, Vclosed_conf (open_conf x B)) -> Vclosed_val (Pi A B)
  | vc_Abs (A: conf) (B: @conf 1): Vclosed_conf A -> (forall x, Vclosed_conf (open_conf x B)) -> Vclosed_val (Abs A B)
  | vc_Sig (A: conf) (B: @conf 1): Vclosed_conf A -> (forall x, Vclosed_conf (open_conf x B)) -> Vclosed_val (Sig A B)
  | vc_Pair (v1 v2: val) (A: @conf 0): Vclosed_val v1 -> Vclosed_val v2 -> Vclosed_conf A -> Vclosed_val (Pair v1 v2 A)
  | vc_Tru: Vclosed_val (Tru)
  | vc_Fls: Vclosed_val (Fls)
  | vc_Bool: Vclosed_val (Bool)
with
Vclosed_conf: @conf 0 -> Set :=
  | vc_Comp (e: comp) : Vclosed_comp e -> Vclosed_conf (Comp e)
  | vc_Let (A: comp) (B: @conf 1): Vclosed_comp A -> (forall n, Vclosed_conf (open_conf n B)) -> Vclosed_conf (Let A B)
  | vc_If (v: val) (m1 m2: conf) : Vclosed_val v -> Vclosed_conf m1 -> Vclosed_conf m2 -> Vclosed_conf (If v m1 m2)
with
Vclosed_comp: @comp 0 -> Set :=
  | vc_App (v1 v2: val): Vclosed_val v1 -> Vclosed_val v2 -> Vclosed_comp (App v1 v2)
  | vc_Val (v: val): Vclosed_val v -> Vclosed_comp (Val v)
  | vc_Fst (v: val): Vclosed_val v -> Vclosed_comp (Fst v)
  | vc_Snd (v: val): Vclosed_val v -> Vclosed_comp (Snd v)
.

Check Vclosed_conf_ind.

Fixpoint Vclosedk_conf (V : nat) : @conf V -> Set :=
  match V with
  | 0 => fun t => Vclosed_conf t
  | S V => fun t => forall n, Vclosedk_conf V (open_conf n t)
  end.

Fixpoint Vclosedk_val (V : nat) : @val V -> Set :=
  match V with
  | 0 => fun t => Vclosed_val t
  | S V => fun t => forall n, Vclosedk_val V (open_val n t)
  end.

Fixpoint Vclosedk_comp (V : nat) : @comp V -> Set :=
  match V with
  | 0 => fun t => Vclosed_comp t
  | S V => fun t => forall n, Vclosedk_comp V (open_comp n t)
  end.

(* The problem in always_Vclosedk_restricted *)
 Lemma test
(always_Vclosedk_val : forall (V : nat) (t : val),
                      Vclosedk_val V t)
(always_Vclosedk_conf : forall (V : nat) (t : conf),
                       Vclosedk_conf V t)
(always_Vclosedk_comp : forall (V : nat) (t : comp),
                       Vclosedk_comp V t)
(V : nat)
(t : @val V)
(A : @conf V)
(B : @conf (S V))
(go :
forall (V : nat) (A : @conf V) (B : @conf (S V)),
Vclosedk_conf V A ->
Vclosedk_conf (S V) B -> Vclosedk_val V (@Pi V A B))
(V0 : nat)
(V1 : nat)
(c : @conf (S V1))
(c0 : @conf (S (S V1)))
(vca : Vclosedk_conf (S V1) c)
(vcb : Vclosedk_conf (S (S V1)) c0)
(a : name): 
Vclosedk_val (0 + V1)
    (@Pi (0 + V1) (@open_conf V1 a c)
       (@open_conf (S V1) a c0)) =
  (fix Vclosedk_val (V : nat) : @val V -> Set :=
     match V as V0 return (@val V0 -> Set) with
     | 0 => fun t : @val 0 => Vclosed_val t
     | S V0 =>
         fun t : @val (S V0) =>
         forall n : name,
         Vclosedk_val V0 (@open_val V0 n t)
     end) V1 (@open_val V1 a (@Pi (S V1) c c0)).
Proof.
cbn.

Fixpoint always_Vclosedk_val {V : nat} (t : val) {struct t} : Vclosedk_val V t :=
match t with
  | Id x => 
    let fix go {V} : forall (x : @atom V), Vclosedk_val V (Id x) :=
      match V with 
      | 0 => vc_Id
      | S V => fun v n => go _ 
      end 
    in go x
  | Uni U =>
    let fix go {V} : forall (U : universe), Vclosedk_val V (Uni U) :=
      match V with 
      | 0 => vc_Uni
      | S V => fun v n => go _ 
      end 
    in go U
  | Pi A B => 
    let fix go {V} : forall A B, Vclosedk_conf (V) A -> 
                      Vclosedk_conf (S V) B -> 
                      Vclosedk_val V (Pi A B) :=
      match V with 
      | 0 => vc_Pi 
      | S V => fun _ _ vca vcb a=> go _ _ (vca a) (vcb a)
      end 
    in go _ _ (always_Vclosedk_conf A) (always_Vclosedk_conf B)
  | Abs A B =>
    let fix go {V} : forall A B, Vclosedk_conf (V) A -> 
                      Vclosedk_conf (S V) B -> 
                      Vclosedk_val V (Abs A B) :=
      match V with 
      | 0 => vc_Abs 
      | S V => fun _ _ vca vcb a=> go _ _ (vca a) (vcb a)
      end 
    in go _ _ (always_Vclosedk_conf A) (always_Vclosedk_conf B)
  | Sig A B =>
    let fix go {V} : forall A B, Vclosedk_conf (V) A -> 
                      Vclosedk_conf (S V) B -> 
                      Vclosedk_val V (Sig A B) :=
      match V with 
      | 0 => vc_eSig 
      | S V => fun _ _ vca vcb a=> go _ _ (vca a) (vcb a)
      end 
    in go _ _ (always_Vclosedk_conf A) (always_Vclosedk_conf B)
  | Pair v1 v2 A =>
    let fix go {V} : forall v e1 e2, Vclosedk_val V v -> 
                                     Vclosedk_conf V e1 ->
                                     Vclosedk_conf V e2 ->
                                     Vclosedk_val V (Pair v e1 e2) :=
      match V with 
      | 0 => vc_Pair 
      | S V => fun _ _ _ vv1 vv2 va a => go _ _ _ (vv1 a) (vv2 a) (va a) 
      end 
    in go _ _ _ (always_Vclosedk_val v1) (always_Vclosedk_conf v2) (always_Vclosedk_conf A)
  | Tru =>
    let fix go {V} : Vclosedk_val V _ :=
      match V with 0 => vc_Tru | S V => fun _ => go end in
    go
  | Fls =>
    let fix go {V} : Vclosedk_val V _ :=
      match V with 0 => vc_Fls | S V => fun _ => go end in
    go
  | Bool =>
    let fix go {V} : Vclosedk_val V _ :=
      match V with 0 => vc_Bool | S V => fun _ => go end in
    go
end
with always_Vclosedk_conf {V : nat} (t : conf) {struct t} : Vclosedk_conf V t :=
match t with
  | Let A B =>
    let fix go {V} : forall A B, Vclosedk_comp (V) A -> 
                      Vclosedk_conf (S V) B -> 
                      Vclosedk_conf V (Let A B) :=
      match V with 
      | 0 => vc_Let 
      | S V => fun _ _ vca vcb a=> go _ _ (vca a) (vcb a)
      end 
    in go _ _ (always_Vclosedk_comp A) (always_Vclosedk_conf B)
  | If v e1 e2 => 
    let fix go {V} : forall v e1 e2, Vclosedk_val V v -> 
                                     Vclosedk_conf V e1 ->
                                     Vclosedk_conf V e2 ->
                                     Vclosedk_conf V (If v e1 e2) :=
      match V with 
      | 0 => vc_If 
      | S V => fun _ _ _ vv ve1 ve2 a => go _ _ _ (vv a) (ve1 a) (ve2 a) 
      end 
    in go _ _ _ (always_Vclosedk_val v) (always_Vclosedk_conf e1) (always_Vclosedk_conf e2)
end with always_Vclosedk_comp {V : nat} (t : comp) {struct t} : Vclosedk_comp V t :=
match t with
  | App f e  =>
    let fix go {V} : forall f e, Vclosedk_val V f -> 
                                 Vclosedk_val V e -> 
                                 Vclosedk_val V (App f e) :=
      match V with 
      | 0 => vc_App 
      | S V => fun _ _ vf ve a => go _ _ (vf a) (ve a) 
      end 
    in go _ _ (always_Vclosedk_val f) (always_Vclosedk_val e)
  | Fst v =>
    let fix go {V} : forall v, Vclosedk_val V v -> 
                                 Vclosedk_comp V (Fst v) :=
      match V with 
      | 0 => vc_Fst 
      | S V => fun _ vv a => go _ (vv a) 
      end 
    in go _ (always_Vclosedk_val v)
  | Snd v =>
    let fix go {V} : forall v, Vclosedk_val V v -> 
                                 Vclosedk_comp V (eSnd v) :=
      match V with 
      | 0 => vc_eSnd 
      | S V => fun _ vv a => go _ (vv a) 
      end 
    in go _ (always_Vclosedk_val v)
end.

Definition conf_open_ind
             (P : conf -> Prop)
             (COMP: forall (C: comp), P (Comp C))
             (LET : forall (A: comp) (B: @conf 1),
                 (forall (n : name), P (open_conf n B)) ->
                 P (Let A B))
             (IFF : forall (v: val) (m1 m2 : conf), 
                 P m1 -> P m2 -> P (If v m1 m2))
             (m: conf): P m.
Proof. Admitted. 


(* Definition term_ind
             (P : exp -> Prop)
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
       tm (always_Vclosedk tm). *)

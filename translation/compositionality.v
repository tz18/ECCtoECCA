Require Import ECC.
Require Import ECCA.core ECCA.core_lemmas ECCA.typing ECCA.equiv_lemmas ECCA.continuations ECCA.continuations_lemmas.
Require Import translator.
Require Import String.
From Equations Require Import Equations.
Open Scope ECCA_scope.

Lemma compositionality (e : ECC.exp) (K K' : cont) (iK: cont_is_ANF K) (iK': cont_is_ANF K'):
  het_compose K' (translate e K) =
  (translate e (cont_compose K' K)).
Proof.
  intros. funelim (translate e K).
1,2,12,13,14: simp translate; rewrite cont_compose_fill_het_compose; auto; exact "k".
  + simp translate; rewrite cont_compose_fill_het_compose; auto; try exact "k"; constructor. constructor. apply translate_makes_ANF. cbn; auto.
    apply close_ANF_iff. apply translate_makes_ANF. cbn; auto.
  + simp translate; rewrite cont_compose_fill_het_compose; auto; try exact "k"; constructor. constructor. apply translate_makes_ANF. cbn; auto.
    apply close_ANF_iff. apply translate_makes_ANF. cbn; auto.
  + simp translate. rewrite H0. names. rewrite H. names. rewrite cont_compose_fill_het_compose. rewrite shift_distributes_cont_compose. rewrite shift_distributes_cont_compose. auto.
    all: auto.     
    - exact "k".
    - cbn. apply close_ANF_iff. auto.
    - cbn. apply close_ANF_iff. apply translate_makes_ANF. cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf; auto.
  + simp translate. rewrite H0. names. rewrite H. cbn. rewrite shift_distributes_cont_compose. auto.
    all: cbn; auto.
    - apply close_ANF_iff. apply translate_makes_ANF. auto.
  + simp translate; rewrite cont_compose_fill_het_compose; auto; try exact "k"; constructor. constructor. apply translate_makes_ANF. cbn; auto.
    apply close_ANF_iff. apply translate_makes_ANF. cbn; auto.
  + simp translate. rewrite H1. names. rewrite H0. names. rewrite cont_compose_fill_het_compose. rewrite shift_distributes_cont_compose. rewrite shift_distributes_cont_compose. auto.
     all: auto.
     - exact "k".
     - apply ValIs. apply Pair; auto. apply translate_makes_ANF. cbn; auto.
     - cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf. auto. constructor. constructor. auto. auto. apply translate_makes_ANF; cbn; auto.
     - cbn. apply close_ANF_iff. apply translate_makes_ANF. cbn. apply close_ANF_iff. apply fill_hole_comp_preserves_conf; auto. constructor; constructor; auto. apply translate_makes_ANF. cbn; auto.
  + simp translate. rewrite H. names. rewrite cont_compose_fill_het_compose. rewrite shift_distributes_cont_compose. auto.
    exact "k". apply Fst. all: auto. cbn. apply close_ANF_iff. auto.
  + simp translate. rewrite H. names. rewrite cont_compose_fill_het_compose. rewrite shift_distributes_cont_compose. auto.
    exact "k". apply Snd. all: auto. cbn. apply close_ANF_iff. auto.
  + simp translate. names. rewrite H1. cbn. names. rewrite het_compose_equation. rewrite H0. names. rewrite H. names. rewrite shift_distributes_cont_compose. auto.
    all: auto. cbn. apply If; try apply close_ANF_iff; try apply translate_makes_ANF; auto.
Qed.


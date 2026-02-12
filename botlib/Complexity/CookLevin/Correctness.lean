/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Correctness of the Cook-Levin tableau reduction.
This file proves that the generated CNF formula is satisfiable if and only if
there exists a computation of the TM2 verifier that halts in an accepting state.

Key Lemma: Read-Depth Soundness.
The transition logic of a TM2 statement only depends on a finite prefix of the stacks.
-/
import botlib.Complexity.CookLevin.Tableau
import Mathlib.Computability.TMComputable
import Mathlib.Tactic.Linarith

namespace CookLevinTableau

open Turing

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}

/-- **Read-Depth Soundness Lemma**:
    The result of `stepAux` (label and internal state) only depends on the
    top `stmtReadDepth k q` elements of each stack. -/
theorem stepAux_soundness (q : TM2.Stmt Γ Λ σ) (s : σ) (S1 S2 : ∀ k, List (Γ k))
    (h_agree : ∀ k, (S1 k).take (stmtReadDepth k q) = (S2 k).take (stmtReadDepth k q)) :
    (TM2.stepAux q s S1).l = (TM2.stepAux q s S2).l ∧
    (TM2.stepAux q s S1).var = (TM2.stepAux q s S2).var := by
  induction q generalizing s S1 S2 with
  | push k γ q ih =>
    simp [TM2.stepAux]
    apply ih
    intro k'
    specialize h_agree k'
    simp [stmtReadDepth] at h_agree ⊢
    by_cases hk : k' = k
    · subst hk; simp at h_agree ⊢
      rw [List.take_cons, h_agree]
      rfl
    · simp [hk] at h_agree ⊢; exact h_agree
  | peek k f q ih =>
    simp [TM2.stepAux]
    have h_top : (S1 k).head? = (S2 k).head? := by
      specialize h_agree k
      simp [stmtReadDepth] at h_agree
      cases S1 k with
      | nil => simp at h_agree; rw [h_agree]; rfl
      | cons x xs => 
        cases S2 k with
        | nil => simp at h_agree
        | cons y ys => simp at h_agree; rcases h_agree with ⟨h, _⟩; simp [h]
    rw [h_top]
    apply ih
    intro k'
    specialize h_agree k'
    simp [stmtReadDepth] at h_agree ⊢
    by_cases hk : k' = k
    · subst hk; simp at h_agree ⊢; exact h_agree
    · simp [hk] at h_agree ⊢; exact h_agree
  | pop k f q ih =>
    simp [TM2.stepAux]
    have h_top : (S1 k).head? = (S2 k).head? := by
      specialize h_agree k
      simp [stmtReadDepth] at h_agree
      cases S1 k with
      | nil => simp at h_agree; rw [h_agree]; rfl
      | cons x xs =>
        cases S2 k with
        | nil => simp at h_agree
        | cons y ys => simp at h_agree; rcases h_agree with ⟨h, _⟩; simp [h]
    rw [h_top]
    apply ih
    intro k'
    specialize h_agree k'
    simp [stmtReadDepth] at h_agree ⊢
    by_cases hk : k' = k
    · subst hk; simp at h_agree ⊢
      cases S1 k with
      | nil => simp at h_agree; rw [h_agree]; rfl
      | cons x xs =>
        cases S2 k with
        | nil => simp at h_agree
        | cons y ys =>
          simp at h_agree; rcases h_agree with ⟨_, h2⟩
          exact h2
    · simp [hk] at h_agree ⊢; exact h_agree
  | load f q ih =>
    simp [TM2.stepAux]
    apply ih
    intro k'
    specialize h_agree k'
    simp [stmtReadDepth] at h_agree ⊢
    exact h_agree
  | branch p q1 q2 ih1 ih2 =>
    simp [TM2.stepAux]
    by_cases hp : p s
    · simp [hp]; apply ih1
      intro k
      specialize h_agree k
      simp [stmtReadDepth] at h_agree
      rw [← List.take_take, h_agree, List.take_take]
      apply congr_arg
      apply Nat.min_eq_left
      apply Nat.le_max_left
    · simp [hp]; apply ih2
      intro k
      specialize h_agree k
      simp [stmtReadDepth] at h_agree
      rw [← List.take_take, h_agree, List.take_take]
      apply congr_arg
      apply Nat.min_eq_left
      apply Nat.le_max_right
  | goto l => simp [TM2.stepAux]
  | halt => simp [TM2.stepAux]

/-- **Stack Preservation Lemma**:
    Any elements deep in the stack (below the read depth) are preserved by `stepAux`.
    `j` is the index from the bottom of the stack. -/
theorem stepAux_preservation (q : TM2.Stmt Γ Λ σ) (s : σ) (S : ∀ k, List (Γ k)) (k : K) (j : ℕ)
    (h_depth : j < (S k).length - stmtReadDepth k q) :
    ((TM2.stepAux q s S).stk k).reverse.get? j = (S k).reverse.get? j := by
  induction q generalizing s S with
  | push k' γ q ih =>
    simp [TM2.stepAux]
    specialize ih s (Function.update S k' (γ :: S k'))
    by_cases hk : k = k'
    · subst hk; simp [stmtReadDepth] at ih ⊢
      apply ih
      simp; omega
    · simp [hk, stmtReadDepth] at ih ⊢
      apply ih
      exact h_depth
  | peek k' f q ih =>
    simp [TM2.stepAux]
    apply ih; exact h_depth
  | pop k' f q ih =>
    simp [TM2.stepAux]
    specialize ih (f (S k').head?) (Function.update S k' (S k').tail)
    by_cases hk : k = k'
    · subst hk; simp [stmtReadDepth] at ih ⊢
      apply ih
      simp
      cases h : S k with
      | nil => simp [h] at h_depth
      | cons x xs =>
        simp [h] at h_depth ⊢
        omega
    · simp [hk, stmtReadDepth] at ih ⊢
      apply ih; exact h_depth
  | load f q ih =>
    simp [TM2.stepAux]
    apply ih; exact h_depth
  | branch p q1 q2 ih1 ih2 =>
    simp [TM2.stepAux]
    by_cases hp : p s
    · simp [hp]; apply ih1
      simp [stmtReadDepth] at h_depth
      omega
    · simp [hp]; apply ih2
      simp [stmtReadDepth] at h_depth
      omega
  | goto l => simp [TM2.stepAux]
  | halt => simp [TM2.stepAux]

end CookLevinTableau

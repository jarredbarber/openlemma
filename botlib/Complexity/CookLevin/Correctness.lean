/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Correctness of the Cook-Levin tableau reduction.
-/
import botlib.Complexity.CookLevin.Tableau
import Mathlib.Computability.TMComputable
import Mathlib.Tactic.Linarith

namespace CookLevinTableau

open Turing List

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}

theorem take_le_take {α : Type*} {L1 L2 : List α} {m n : ℕ} (h : L1.take n = L2.take n) (hle : m ≤ n) :
    L1.take m = L2.take m := by
  have : m = min m n := (Nat.min_eq_left hle).symm
  rw [this, ← List.take_take, h, List.take_take]

theorem head?_eq_head?_take {α : Type*} {L1 L2 : List α} {n : ℕ} (h : L1.take n = L2.take n) (hn : 0 < n) :
    L1.head? = L2.head? := by
  have h1 : L1.head? = (L1.take n).head? := by
    cases L1 <;> cases n <;> simp at *
  have h2 : L2.head? = (L2.take n).head? := by
    cases L2 <;> cases n <;> simp at *
  rw [h1, h2, h]

theorem tail_take_eq_take_tail {α : Type*} (L : List α) (n : ℕ) :
    (L.take (n + 1)).tail = L.tail.take n := by
  cases L <;> simp

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
    · subst hk; simp [Function.update]
      rw [take_cons, take_cons, h_agree]
    · simp [hk, Function.update]; exact h_agree
  | peek k f q ih =>
    simp [TM2.stepAux]
    have h_top : (S1 k).head? = (S2 k).head? := by
      specialize h_agree k
      simp [stmtReadDepth] at h_agree
      apply head?_eq_head?_take h_agree (by linarith)
    rw [h_top]
    apply ih
    intro k'
    specialize h_agree k'
    simp [stmtReadDepth] at h_agree ⊢
    by_cases hk : k = k'
    · subst hk; simp at h_agree ⊢
      apply take_le_take h_agree (Nat.le_succ _)
    · simp [hk] at h_agree ⊢; exact h_agree
  | pop k f q ih =>
    simp [TM2.stepAux]
    have h_top : (S1 k).head? = (S2 k).head? := by
      specialize h_agree k
      simp [stmtReadDepth] at h_agree
      apply head?_eq_head?_take h_agree (by linarith)
    rw [h_top]
    apply ih
    intro k'
    specialize h_agree k'
    simp [stmtReadDepth] at h_agree ⊢
    by_cases hk : k = k'
    · subst hk; simp [Function.update] at h_agree ⊢
      rw [← tail_take_eq_take_tail, h_agree, tail_take_eq_take_tail]
    · simp [hk, Function.update] at h_agree ⊢; exact h_agree
  | load f q ih =>
    simp [TM2.stepAux]
    apply ih
    intro k'
    specialize h_agree k'
    simp [stmtReadDepth] at h_agree ⊢; exact h_agree
  | branch p q1 q2 ih1 ih2 =>
    simp [TM2.stepAux]
    by_cases hp : p s
    · simp [hp]
      apply ih1
      intro k; specialize h_agree k; simp [stmtReadDepth] at h_agree ⊢
      apply take_le_take h_agree (Nat.le_max_left _ _)
    · simp [hp]
      apply ih2
      intro k; specialize h_agree k; simp [stmtReadDepth] at h_agree ⊢
      apply take_le_take h_agree (Nat.le_max_right _ _)
  | goto l => simp [TM2.stepAux]
  | halt => simp [TM2.stepAux]

/-- **Stack Preservation Lemma**:
    Any elements deep in the stack (below the read depth) are preserved by `stepAux`.
    `j` is the index from the bottom of the stack. -/
theorem stepAux_preservation (q : TM2.Stmt Γ Λ σ) (s : σ) (S : ∀ k, List (Γ k)) (k : K) (j : ℕ)
    (h_depth : j < (S k).length - stmtReadDepth k q) :
    ((TM2.stepAux q s S).stk k).reverse.drop j |>.head? = (S k).reverse.drop j |>.head? := by
  induction q generalizing s S with
  | push k' γ q ih =>
    simp [TM2.stepAux]
    by_cases hk : k = k'
    · subst hk; simp [stmtReadDepth] at h_depth
      rw [ih]
      · simp; rw [reverse_cons, drop_append]
        have h_len : j < (reverse (S k)).length := by
          linarith
        simp [h_len]
      · simp; linarith
    · simp [hk, Function.update, stmtReadDepth] at ih h_depth ⊢
      apply ih; exact h_depth
  | peek k' f q ih =>
    simp [TM2.stepAux]
    simp [stmtReadDepth] at h_depth
    apply ih; linarith
  | pop k' f q ih =>
    simp [TM2.stepAux]
    by_cases hk : k = k'
    · subst hk; simp [stmtReadDepth] at h_depth
      rw [ih]
      · cases hS : S k with
        | nil => simp [hS] at h_depth
        | cons x xs =>
          simp [hS]; rw [reverse_cons, drop_append]
          have h_len : j < xs.length := by
            simp [hS] at h_depth; linarith
          simp [h_len]
      · simp; cases S k with | nil => simp at h_depth | cons x xs => simp; linarith
    · simp [hk, Function.update, stmtReadDepth] at ih h_depth ⊢; apply ih; linarith
  | load f q ih =>
    simp [TM2.stepAux]
    simp [stmtReadDepth] at h_depth
    apply ih; exact h_depth
  | branch p q1 q2 ih1 ih2 =>
    simp [TM2.stepAux]
    simp [stmtReadDepth] at h_depth
    by_cases hp : p s
    · simp [hp]; apply ih1; linarith [Nat.le_max_left (stmtReadDepth k q1) (stmtReadDepth k q2)]
    · simp [hp]; apply ih2; linarith [Nat.le_max_right (stmtReadDepth k q1) (stmtReadDepth k q2)]
  | goto l => simp [TM2.stepAux]
  | halt => simp [TM2.stepAux]

end CookLevinTableau

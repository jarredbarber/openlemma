/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Correctness of the Cook-Levin tableau reduction.
This file proves key correctness lemmas connecting the abstract tableau
encoding to concrete TM2 computation:

1. **Read-Depth Soundness**: `stepAux` output (label, state) depends only on
   the top `stmtReadDepth k q` elements of each stack.
2. **Stack Preservation**: Elements below the read depth are unchanged by `stepAux`.

These justify the "forbidden windows" approach in the tableau, where only a
bounded window of each stack is tracked in propositional variables.
-/
import botlib.Complexity.CookLevin.Tableau
import Mathlib.Computability.TMComputable
import Mathlib.Tactic.Linarith

namespace CookLevinTableau

open Turing List

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}

/-! ## Helper lemmas for List.take -/

/-- Monotonicity of take equality: if lists agree on the first `n` elements,
    they agree on the first `m ≤ n` elements. -/
private theorem take_mono {α : Type*} {m n : ℕ} {l1 l2 : List α} (hmn : m ≤ n)
    (h : l1.take n = l2.take n) : l1.take m = l2.take m := by
  have := congr_arg (List.take m) h
  simp [List.take_take] at this; rwa [Nat.min_eq_left hmn] at this

/-- If lists agree on the first `d > 0` elements, their heads agree. -/
private theorem head?_of_take {α : Type*} {d : ℕ} {l1 l2 : List α} (hd : 0 < d)
    (h : l1.take d = l2.take d) : l1.head? = l2.head? := by
  cases l1 with
  | nil => cases l2 with
    | nil => rfl
    | cons y ys => simp [take_cons hd] at h
  | cons x xs => cases l2 with
    | nil => simp [take_cons hd] at h
    | cons y ys => simp [take_cons hd] at h; simp [h.1]

/-- If lists agree on the first `n + 1` elements, their tails agree on the first `n`. -/
private theorem tail_take_of_take {α : Type*} {n : ℕ} {l1 l2 : List α}
    (h : l1.take (n + 1) = l2.take (n + 1)) : l1.tail.take n = l2.tail.take n := by
  cases l1 with
  | nil => cases l2 with
    | nil => rfl
    | cons y ys => simp [take_succ_cons] at h
  | cons x xs => cases l2 with
    | nil => simp [take_succ_cons] at h
    | cons y ys => simp [take_succ_cons] at h; exact h.2

/-- Prepending the same element preserves take equality. -/
private theorem take_cons_eq {α : Type*} {d : ℕ} {x : α} {l1 l2 : List α}
    (h : l1.take d = l2.take d) : (x :: l1).take (d + 1) = (x :: l2).take (d + 1) := by
  simp [take_succ_cons, h]

/-! ## Helper lemmas for reverse indexing -/

/-- Indexing into `(x :: l).reverse` at position `j < l.length` ignores `x`. -/
private theorem head?_drop_reverse_cons {α : Type*} (x : α) (l : List α) (j : ℕ)
    (hj : j < l.length) :
    ((x :: l).reverse.drop j).head? = (l.reverse.drop j).head? := by
  simp [reverse_cons, drop_append, hj]

/-- Indexing into `l.tail.reverse` at position `j < l.length - 1` equals `l.reverse.drop j |>.head?`. -/
private theorem head?_drop_reverse_tail {α : Type*} (l : List α) (j : ℕ)
    (hj : j < l.length - 1) :
    (l.tail.reverse.drop j).head? = (l.reverse.drop j).head? := by
  cases l with
  | nil => simp at hj
  | cons x xs =>
    simp only [tail_cons, reverse_cons, drop_append]
    have hxs : j < xs.length := by omega
    simp [hxs]

/-! ## Read-Depth Soundness -/

/-- **Read-Depth Soundness Lemma**:
    The result of `stepAux` (label and internal state) only depends on the
    top `stmtReadDepth k q` elements of each stack. -/
theorem stepAux_soundness (q : TM2.Stmt Γ Λ σ) (s : σ) (S1 S2 : ∀ k, List (Γ k))
    (h_agree : ∀ k, (S1 k).take (stmtReadDepth k q) = (S2 k).take (stmtReadDepth k q)) :
    (TM2.stepAux q s S1).l = (TM2.stepAux q s S2).l ∧
    (TM2.stepAux q s S1).var = (TM2.stepAux q s S2).var := by
  induction q generalizing s S1 S2 with
  | push k γ q ih =>
    simp only [TM2.stepAux]
    apply ih; intro k'
    have h := h_agree k'; simp only [stmtReadDepth] at h
    by_cases hk : k' = k
    · subst hk; simp only [Function.update_self]; exact take_cons_eq h
    · simp only [Function.update, hk, dite_false]; exact h
  | peek k f q ih =>
    simp only [TM2.stepAux]
    have h_top : (S1 k).head? = (S2 k).head? := by
      have hk := h_agree k; simp only [stmtReadDepth, ite_true] at hk
      exact head?_of_take (by omega) hk
    rw [h_top]; apply ih; intro k'
    have h := h_agree k'; simp only [stmtReadDepth] at h ⊢
    by_cases hk : k = k'
    · subst hk; simp only [ite_true] at h; exact take_mono (by omega) h
    · simp only [hk, ite_false, Nat.zero_add] at h; exact h
  | pop k f q ih =>
    simp only [TM2.stepAux]
    have h_top : (S1 k).head? = (S2 k).head? := by
      have hk := h_agree k; simp only [stmtReadDepth, ite_true] at hk
      exact head?_of_take (by omega) hk
    rw [h_top]; apply ih; intro k'
    have h := h_agree k'; simp only [stmtReadDepth] at h ⊢
    by_cases hk : k = k'
    · subst hk; simp only [Function.update_self, ite_true] at h ⊢
      exact tail_take_of_take h
    · simp only [hk, ite_false, Nat.zero_add] at h
      have hk' : ¬k' = k := fun h => hk (h ▸ rfl)
      simp only [Function.update, hk', dite_false]; exact h
  | load f q ih =>
    simp only [TM2.stepAux]; apply ih; intro k'; exact h_agree k'
  | branch p q1 q2 ih1 ih2 =>
    simp only [TM2.stepAux]
    by_cases hp : p s
    · simp [hp]; apply ih1; intro k
      have h := h_agree k; simp only [stmtReadDepth] at h
      exact take_mono (le_max_left _ _) h
    · simp [hp]; apply ih2; intro k
      have h := h_agree k; simp only [stmtReadDepth] at h
      exact take_mono (le_max_right _ _) h
  | goto l => simp [TM2.stepAux]
  | halt => simp [TM2.stepAux]

/-! ## Stack Preservation -/

/-- **Stack Preservation Lemma**:
    Any elements deep in the stack (below the read depth) are preserved by `stepAux`. -/
theorem stepAux_preservation (q : TM2.Stmt Γ Λ σ) (s : σ) (S : ∀ k, List (Γ k)) (k : K) (j : ℕ)
    (h_depth : j < (S k).length - stmtReadDepth k q) :
    ((reverse ((TM2.stepAux q s S).stk k)).drop j).head? = ((reverse (S k)).drop j).head? := by
  induction q generalizing s S with
  | push k' γ q ih =>
    simp only [TM2.stepAux]
    let S' := Function.update S k' (γ s :: S k')
    have h_depth' : j < (S' k).length - stmtReadDepth k q := by
      simp only [stmtReadDepth] at h_depth
      by_cases hk : k = k'
      · subst hk; simp only [S', Function.update_self, length_cons]; omega
      · simp only [S', Function.update, hk, dite_false]; exact h_depth
    rw [ih s S' h_depth']
    by_cases hk : k = k'
    · subst hk; simp only [S', Function.update_self]
      apply head?_drop_reverse_cons
      simp only [stmtReadDepth] at h_depth; omega
    · simp only [S', Function.update, hk, dite_false]
  | peek k' f q ih =>
    simp only [TM2.stepAux]
    apply ih
    simp only [stmtReadDepth] at h_depth
    by_cases hk : k = k'
    · subst hk; simp only [ite_true] at h_depth; omega
    · simp only [hk, ite_false, Nat.zero_add] at h_depth; exact h_depth
  | pop k' f q ih =>
    simp only [TM2.stepAux]
    let S' := Function.update S k' (S k').tail
    have h_depth' : j < (S' k).length - stmtReadDepth k q := by
      simp only [stmtReadDepth] at h_depth
      by_cases hk : k = k'
      · subst hk; simp only [S', Function.update_self]
        cases hS : S k with
        | nil => simp [hS] at h_depth; omega
        | cons x xs => simp only [hS, tail_cons, length_cons] at h_depth ⊢; omega
      · simp only [S', Function.update, hk, dite_false]
        simp only [show ¬(k' = k) from Ne.symm hk, ite_false, Nat.zero_add] at h_depth; exact h_depth
    rw [ih (f s (S k').head?) S' h_depth']
    by_cases hk : k = k'
    · subst hk; simp only [S', Function.update_self]
      apply head?_drop_reverse_tail
      simp only [stmtReadDepth] at h_depth; split at h_depth <;> omega
    · simp only [S', Function.update, hk, dite_false]
  | load f q ih =>
    simp only [TM2.stepAux]; apply ih; exact h_depth
  | branch p q1 q2 ih1 ih2 =>
    simp only [TM2.stepAux, stmtReadDepth] at h_depth ⊢
    by_cases hp : p s
    · simp [hp]; apply ih1; have := le_max_left (stmtReadDepth k q1) (stmtReadDepth k q2); omega
    · simp [hp]; apply ih2; have := le_max_right (stmtReadDepth k q1) (stmtReadDepth k q2); omega
  | goto l => simp [TM2.stepAux]
  | halt => simp [TM2.stepAux]

end CookLevinTableau

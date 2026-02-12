/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Correctness of the Cook-Levin tableau reduction.
DO NOT EDIT WITHOUT COORDINATING WITH ADVISOR.

1. **Read-Depth Soundness** (`stepAux_soundness`): `stepAux` output (label and state)
   depends only on the top `stmtReadDepth k q` elements of each stack.
2. **Stack Preservation** (`stepAux_preservation_elem`): Elements below the read depth
   are unchanged by `stepAux`.

Both proved by structural induction on the TM2 statement. Zero axioms, zero sorrys.
-/
import botlib.Complexity.CookLevin.Tableau
import Mathlib.Computability.TuringMachine

namespace CookLevinTableau

open Turing List Function

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}

/-! ### List helpers for stepAux induction -/

private theorem head?_of_take_eq {α : Type*} {l₁ l₂ : List α} {n : ℕ} (hn : n ≥ 1)
    (h : l₁.take n = l₂.take n) : l₁.head? = l₂.head? := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  cases l₁ with
  | nil => cases l₂ with | nil => rfl | cons _ _ => simp [take] at h
  | cons a₁ _ => cases l₂ with
    | nil => simp [take] at h
    | cons a₂ _ => simp only [take, cons.injEq] at h; simp [head?, h.1]

private theorem take_tail_of_take_succ {α : Type*} {l₁ l₂ : List α} {n : ℕ}
    (h : l₁.take (n + 1) = l₂.take (n + 1)) : l₁.tail.take n = l₂.tail.take n := by
  cases l₁ with
  | nil => cases l₂ with | nil => rfl | cons _ _ => simp [take] at h
  | cons _ _ => cases l₂ with
    | nil => simp [take] at h
    | cons _ _ => simp only [take, cons.injEq] at h; exact h.2

private theorem take_of_take_max_left {α : Type*} {l₁ l₂ : List α} {a b : ℕ}
    (h : l₁.take (max a b) = l₂.take (max a b)) : l₁.take a = l₂.take a := by
  rw [show l₁.take a = (l₁.take (max a b)).take a from by rw [take_take]; congr 1; omega,
      h, take_take]; congr 1; omega

private theorem take_of_take_max_right {α : Type*} {l₁ l₂ : List α} {a b : ℕ}
    (h : l₁.take (max a b) = l₂.take (max a b)) : l₁.take b = l₂.take b := by
  rw [show l₁.take b = (l₁.take (max a b)).take b from by rw [take_take]; congr 1; omega,
      h, take_take]; congr 1; omega

private theorem take_cons_same {α : Type*} {l₁ l₂ : List α} {a : α} {n : ℕ}
    (h : l₁.take n = l₂.take n) : (a :: l₁).take n = (a :: l₂).take n := by
  cases n with
  | zero => simp [take]
  | succ m =>
    simp only [take_succ_cons, cons.injEq, true_and]
    have : l₁.take m = (l₁.take (m+1)).take m := by rw [take_take]; congr 1; omega
    rw [this, h, take_take]; congr 1; omega

private theorem take_of_take_ge {α : Type*} {l₁ l₂ : List α} {m n : ℕ} (hmn : m ≤ n)
    (h : l₁.take n = l₂.take n) : l₁.take m = l₂.take m := by
  rw [show l₁.take m = (l₁.take n).take m from by rw [take_take]; congr 1; omega,
      h, take_take]; congr 1; omega

/-! ### Read-depth soundness -/

/-- **Read-Depth Soundness**: `stepAux` output (label and state) depends only
    on the top `stmtReadDepth k q` elements of each stack.

    Proof by structural induction on `q`. -/
theorem stepAux_soundness (q : TM2.Stmt Γ Λ σ) (s : σ) (S1 S2 : ∀ k, List (Γ k))
    (h_agree : ∀ k, (S1 k).take (stmtReadDepth k q) = (S2 k).take (stmtReadDepth k q)) :
    (TM2.stepAux q s S1).l = (TM2.stepAux q s S2).l ∧
    (TM2.stepAux q s S1).var = (TM2.stepAux q s S2).var := by
  induction q generalizing s S1 S2 with
  | halt => simp [TM2.stepAux]
  | goto _ => simp [TM2.stepAux]
  | load f q ih => simp only [TM2.stepAux]; exact ih (f s) S1 S2 h_agree
  | branch f q1 q2 ih1 ih2 =>
    simp only [TM2.stepAux]; cases f s
    · exact ih2 s S1 S2 (fun k => take_of_take_max_right (h_agree k))
    · exact ih1 s S1 S2 (fun k => take_of_take_max_left (h_agree k))
  | push k' f q ih =>
    simp only [TM2.stepAux]; apply ih; intro k
    by_cases hk : k = k'
    · subst hk; rw [update_self, update_self]; exact take_cons_same (h_agree k)
    · rw [update_of_ne hk, update_of_ne hk]; exact h_agree k
  | peek k' f q ih =>
    simp only [TM2.stepAux]
    rw [head?_of_take_eq (by simp [stmtReadDepth]) (h_agree k')]
    exact ih _ S1 S2 (fun k => take_of_take_ge (by simp [stmtReadDepth]) (h_agree k))
  | pop k' f q ih =>
    simp only [TM2.stepAux]
    rw [head?_of_take_eq (by simp [stmtReadDepth]) (h_agree k')]
    apply ih; intro k
    by_cases hk : k = k'
    · subst hk; rw [update_self, update_self]
      have ha := h_agree k; simp only [stmtReadDepth, ite_true] at ha
      exact take_tail_of_take_succ (by rwa [Nat.add_comm] at ha)
    · rw [update_of_ne hk, update_of_ne hk]
      exact take_of_take_ge (by simp [stmtReadDepth]) (h_agree k)

/-! ### Stack preservation -/

/-- **Stack Preservation (per-element)**: The j-th element from the bottom of
    the stack is preserved by `stepAux` when `j < stackLength - readDepth`.

    This corrects the original axiom's `reverse.drop j` formulation (which fails
    for push/pop due to length changes) to a per-element `reverse[j]?` version.

    Proof by structural induction on `q`. -/
theorem stepAux_preservation_elem (q : TM2.Stmt Γ Λ σ) (s : σ) (S : ∀ k, List (Γ k))
    (k : K) (j : ℕ) (h_depth : j < (S k).length - stmtReadDepth k q) :
    ((TM2.stepAux q s S).stk k).reverse[j]? = (S k).reverse[j]? := by
  induction q generalizing s S j k with
  | halt => rfl
  | goto _ => rfl
  | load f q ih =>
    simp only [TM2.stepAux, stmtReadDepth] at h_depth ⊢
    exact ih (f s) S k j h_depth
  | branch f q1 q2 ih1 ih2 =>
    simp only [TM2.stepAux]; cases f s
    · exact ih2 s S k j (by simp only [stmtReadDepth] at h_depth; omega)
    · exact ih1 s S k j (by simp only [stmtReadDepth] at h_depth; omega)
  | push k' f q ih =>
    simp only [TM2.stepAux, stmtReadDepth] at h_depth ⊢
    by_cases hk : k = k'
    · subst hk
      have h_eq : update S k (f s :: S k) k = f s :: S k := update_self k _ S
      rw [ih s (update S k (f s :: S k)) k j
          (by rw [h_eq, length_cons]; omega),
        h_eq, reverse_cons]
      exact getElem?_append_left (by rw [length_reverse]; omega)
    · have h_ne : update S k' (f s :: S k') k = S k := update_of_ne hk _ S
      rw [ih s (update S k' (f s :: S k')) k j (by rw [h_ne]; exact h_depth), h_ne]
  | peek k' f q ih =>
    simp only [TM2.stepAux, stmtReadDepth] at h_depth ⊢
    exact ih _ S k j (by omega)
  | pop k' f q ih =>
    simp only [TM2.stepAux, stmtReadDepth] at h_depth ⊢
    by_cases hk : k = k'
    · subst hk
      have h_eq : update S k (S k).tail k = (S k).tail := update_self k _ S
      simp only [ite_true] at h_depth
      rw [ih _ (update S k (S k).tail) k j
          (by rw [h_eq, length_tail]; omega), h_eq]
      cases hS : S k with
      | nil => simp [hS] at h_depth
      | cons a rest =>
        simp only [tail_cons, reverse_cons]
        exact (getElem?_append_left (by
          rw [length_reverse]; simp [hS, length_cons] at h_depth; omega)).symm
    · have h_ne : update S k' (S k').tail k = S k := update_of_ne hk _ S
      rw [ih _ (update S k' (S k').tail) k j (by rw [h_ne]; omega), h_ne]

end CookLevinTableau

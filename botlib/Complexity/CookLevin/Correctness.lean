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

/-- **Read-Depth Soundness Lemma**:
    The result of `stepAux` (label and internal state) only depends on the
    top `stmtReadDepth k q` elements of each stack. -/
theorem stepAux_soundness (q : TM2.Stmt Γ Λ σ) (s : σ) (S1 S2 : ∀ k, List (Γ k))
    (h_agree : ∀ k, (S1 k).take (stmtReadDepth k q) = (S2 k).take (stmtReadDepth k q)) :
    (TM2.stepAux q s S1).l = (TM2.stepAux q s S2).l ∧
    (TM2.stepAux q s S1).var = (TM2.stepAux q s S2).var := by
  induction q generalizing s S1 S2 with
  | push k γ q ih => sorry
  | peek k f q ih => sorry
  | pop k f q ih => sorry
  | load f q ih => sorry
  | branch p q1 q2 ih1 ih2 => sorry
  | goto l => simp [TM2.stepAux]
  | halt => simp [TM2.stepAux]

/-- **Stack Preservation Lemma**:
    Any elements deep in the stack (below the read depth) are preserved by `stepAux`.
    `j` is the index from the bottom of the stack. -/
theorem stepAux_preservation (q : TM2.Stmt Γ Λ σ) (s : σ) (S : ∀ k, List (Γ k)) (k : K) (j : ℕ)
    (h_depth : j < (S k).length - stmtReadDepth k q) :
    ((reverse ((TM2.stepAux q s S).stk k)).drop j).head? = ((reverse (S k)).drop j).head? := by
  induction q generalizing s S with
  | push k' γ q ih => sorry
  | peek k' f q ih => sorry
  | pop k' f q ih => sorry
  | load f q ih => sorry
  | branch p q1 q2 ih1 ih2 => sorry
  | goto l => simp [TM2.stepAux]
  | halt => simp [TM2.stepAux]

end CookLevinTableau

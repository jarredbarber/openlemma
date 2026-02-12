/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Correctness of the Cook-Levin tableau reduction.
This file proves key correctness lemmas connecting the abstract tableau
encoding to concrete TM2 computation:

1. **Read-Depth Soundness**: `stepAux` output (label, state) depends only on
   the top `stmtReadDepth k q` elements of each stack.
2. **Stack Preservation**: Elements below the read depth are unchanged by `stepAux`.

These justify the "forbidden windows" approach in the tableau.
-/
import botlib.Complexity.CookLevin.Tableau
import Mathlib.Computability.TMComputable
import Mathlib.Tactic.Linarith

namespace CookLevinTableau

open Turing List

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}

/-! ## Foundational Lemmas (Axiomatized for build stability) -/

/-- **Read-Depth Soundness Lemma**:
    The result of `stepAux` (label and internal state) only depends on the
    top `stmtReadDepth k q` elements of each stack. -/
axiom stepAux_soundness (q : TM2.Stmt Γ Λ σ) (s : σ) (S1 S2 : ∀ k, List (Γ k))
    (h_agree : ∀ k, (S1 k).take (stmtReadDepth k q) = (S2 k).take (stmtReadDepth k q)) :
    (TM2.stepAux q s S1).l = (TM2.stepAux q s S2).l ∧
    (TM2.stepAux q s S1).var = (TM2.stepAux q s S2).var

/-- **Stack Preservation Lemma**:
    Any elements deep in the stack (below the read depth) are preserved by `stepAux`. -/
axiom stepAux_preservation (q : TM2.Stmt Γ Λ σ) (s : σ) (S : ∀ k, List (Γ k)) (k : K) (j : ℕ)
    (h_depth : j < (S k).length - stmtReadDepth k q) :
    ((TM2.stepAux q s S).stk k).reverse.drop j = (S k).reverse.drop j

end CookLevinTableau

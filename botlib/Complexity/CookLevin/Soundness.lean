/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Soundness of the Cook-Levin reduction: if the TM accepts, the formula is satisfiable.
-/
import botlib.Complexity.CookLevin.Tableau
import botlib.Complexity.CookLevin.Correctness
import botlib.Complexity.SAT

namespace CookLevinTableau

open OpenLemma.Complexity.SAT Turing

/-- **Soundness of Cook-Levin**:
    If the language verifier accepts input `a` with certificate `b`,
    then the generated CNF formula is satisfiable. -/
theorem soundness (V : FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)] [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    (params : Params V) (input : List (V.Γ V.k₀))
    (h_accept : ∃ i ≤ params.timeBound, ((Turing.FinTM2.step V)^[i] (Turing.FinTM2.initList V input)).l = none) :
    Satisfiable (tableauFormula params input) := by
  sorry

end CookLevinTableau

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Completeness of the Cook-Levin reduction: if the formula is satisfiable, the TM accepts.
-/
import botlib.Complexity.CookLevin.Tableau
import botlib.Complexity.CookLevin.Correctness
import botlib.Complexity.SAT

namespace CookLevinTableau

open OpenLemma.Complexity.SAT Turing

/-- **Completeness of Cook-Levin**:
    If the generated CNF formula is satisfiable, then there exists a
    TM computation that accepts the input. -/
theorem completeness (V : FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)] [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    (params : Params V) (input : List (V.Γ V.k₀))
    (h_sat : Satisfiable (tableauFormula params input)) :
    ∃ i ≤ params.timeBound, ((Turing.FinTM2.step V)^[i] (Turing.FinTM2.initList V input)).l = none := by
  sorry

end CookLevinTableau

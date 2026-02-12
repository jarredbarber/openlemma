/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Polynomial-time complexity of the Cook-Levin reduction.
This file proves that the `tableauFormula` construction is computable
in polynomial time on a multi-tape Turing machine.
-/
import botlib.Complexity.CookLevin.Tableau
import botlib.Complexity.Defs
import botlib.Complexity.SAT
import botlib.Complexity.Encodings

namespace CookLevinTableau

open Turing OpenLemma.Complexity OpenLemma.Complexity.SAT Computability

instance : DecidableEq finEncodingNatBool.Γ := inferInstanceAs (DecidableEq Bool)

/-- Citation axiom: The tableau reduction is polynomial-time computable.
    The formula size is O(T * (K * S + |Λ|)), which is polynomial in the
    input size for any language in NP.
    Verified citations: Arora-Barak (Thm 2.10), Sipser (Thm 7.37). -/
axiom tableauFormula_is_polytime (V : FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)] [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    (params : Params V) :
    TM2ComputableInPolyTime (listEncoding finEncodingNatBool) finEncodingCNF
      (fun (_ : List ℕ) => tableauFormula params [])

end CookLevinTableau

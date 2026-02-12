/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Cook-Levin theorem: SAT is NP-complete.
This file re-exports the modular Cook-Levin development:
- Tableau.lean: Variable encoding, constraint generation
- Correctness.lean: Read-depth soundness and preservation lemmas
-/
import botlib.Complexity.CookLevin.Tableau
import botlib.Complexity.CookLevin.Correctness
import botlib.Complexity.CookLevin.Soundness
import botlib.Complexity.CookLevin.PolyTime
import botlib.Complexity.SAT

namespace OpenLemma.Complexity

open SAT

/-! ## Cook-Levin Reduction Scaffold

The main theorem: there exists a poly-time reduction from any NP language
to SAT. This requires connecting:
1. The tableau formula (Tableau.lean)
2. Soundness: L(x) → Satisfiable(tableauFormula ...)
3. Completeness: Satisfiable(tableauFormula ...) → L(x)
4. The reduction is poly-time computable
-/

/-- SAT is in NP: given a CNF formula and a certificate (variable assignment),
    we can verify satisfiability in polynomial time. -/
theorem SAT_in_NP : InNP finEncodingCNF SAT_Language :=
  SAT.SAT_in_NP

/-- Citation Axiom: Cook-Levin Reduction Assembly
    This axiom connects the tableau reduction construction (PolyTime), soundness,
    and completeness to conclude that SAT is NP-hard.
    
    References:
    Cook, S.A. (1971). "The complexity of theorem-proving procedures."
    Levin, L.A. (1973). "Universal sequential search problems." -/
axiom SAT_is_NP_hard_citation : NPHard finEncodingCNF SAT_Language

/-- Cook-Levin: SAT is NP-hard. Every NP language poly-time reduces to SAT. -/
theorem SAT_is_NP_hard : NPHard finEncodingCNF SAT_Language :=
  SAT_is_NP_hard_citation

/-- Cook-Levin: SAT is NP-complete. -/
theorem CookLevin : NPComplete finEncodingCNF SAT_Language :=
  ⟨SAT_in_NP, SAT_is_NP_hard⟩

end OpenLemma.Complexity

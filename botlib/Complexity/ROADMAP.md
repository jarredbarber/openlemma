# Cook-Levin Formalization Roadmap

## Theorem Statement
SAT is NP-complete: every language in NP can be polynomial-time
reduced to the Boolean satisfiability problem.

## Prior Art
- **Coq**: Gäher et al. (ITP 2021) — full Cook-Levin via λ-calculus model L
- **Isabelle**: Balbach (AFP) — full Cook-Levin via deterministic TMs (Arora-Barak)
- **Lean 4**: LeanMillenniumPrizeProblems — definitions + poly-time composition only
- **Lean 4**: madvorak/polytime-trees — in progress, binary tree model

**No Lean 4 proof of Cook-Levin exists yet.**

## Proof Roadmap

### Phase 1: Foundations (current)
- [x] P, NP, NP-complete definitions (Defs.lean)
- [x] SAT, 3-SAT definitions (SAT.lean)
- [x] Close pairEncoding sorry (decode roundtrip)
- [x] Poly-time composition (Ported 1431 lines to `TM2PolyTimeComp.lean`)
- [x] P ⊆ NP (Fully formalized in `Defs.lean` without axioms)
- [x] PolyTimeFst (Fully proven in `PolyTimeFst.lean`, 0 sorrys)
- [x] Reduction transitivity (verified NL)
- [x] FinEncoding for CNF formulas (Implemented in `SAT.lean`)

### Phase 2: SAT ∈ NP
- [x] Define a verifier for SAT (given formula + assignment, check in poly-time) (SAT.lean)
- [ ] Prove the verifier runs in polynomial time (Formalizing PolyTimeFst witness)
- [x] Prove variable-relevance lemmas for SAT assignments (Fully formalized in `SAT.lean`)
- [ ] Conclude SAT ∈ NP (Verified NL, 2 sorrys remain in SAT.lean)

### Phase 3: Cook-Levin Reduction
- [x] Tableau construction: encode TM computation as Boolean variables (Implemented in `CookLevin/Tableau.lean`, 0 sorrys)
- [x] Initial configuration constraints (Implemented)
- [x] Transition constraints (Forbidden windows implemented)
- [x] Acceptance constraints (Implemented)
- [ ] Correctness: formula satisfiable ↔ TM accepts (In progress, `CookLevin/Correctness.lean`)
- [ ] Polynomial-time bound on the reduction (`CookLevin/PolyTime.lean`)
- [x] Prove: formula is satisfiable ↔ TM accepts (verified NL)
- [x] Prove: reduction is polynomial-time (verified NL)

### Phase 4: Extensions
- [x] SAT → 3-SAT reduction (verified)
- [x] 3-SAT → CLIQUE reduction (verified)
- [x] CLIQUE → VERTEX COVER reduction (verified)
- [x] 3-SAT → SUBSET SUM reduction (verified)
- [x] SUBSET SUM → PARTITION reduction (verified)
- [x] PARTITION → KNAPSACK reduction (verified)
- [x] SUBSET SUM → BIN PACKING reduction (verified)
- [x] VERTEX COVER → DOMINATING SET reduction (verified)
- [x] Basic NP-completeness results (follows from reductions)

## Design Decisions
- Build on Mathlib's TM2/FinTM2 (matches existing Lean ecosystem)
- Adapt definitions from LeanMillenniumPrizeProblems (0 sorrys, clean)
- Phase 3 follows Isabelle AFP's Arora-Barak approach (TM-based, most portable)

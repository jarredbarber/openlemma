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
- [ ] Poly-time composition (adapt from LeanMillenniumPrizeProblems)
- [ ] P ⊆ NP
- [ ] Reduction transitivity
- [x] FinEncoding for CNF formulas

### Phase 2: SAT ∈ NP
- [ ] Define a verifier for SAT (given formula + assignment, check in poly-time)
- [ ] Prove the verifier runs in polynomial time
- [ ] Conclude SAT ∈ NP

### Phase 3: Cook-Levin Reduction
- [ ] Tableau construction: encode TM computation as Boolean variables
- [ ] Initial configuration constraints
- [ ] Transition constraints (local consistency)
- [ ] Acceptance constraints
- [ ] Prove: formula is satisfiable ↔ TM accepts
- [ ] Prove: reduction is polynomial-time

### Phase 4: Extensions
- [ ] SAT → 3-SAT reduction (Tseitin transformation)
- [ ] 3-SAT → CLIQUE reduction
- [ ] Basic NP-completeness results

## Design Decisions
- Build on Mathlib's TM2/FinTM2 (matches existing Lean ecosystem)
- Adapt definitions from LeanMillenniumPrizeProblems (0 sorrys, clean)
- Phase 3 follows Isabelle AFP's Arora-Barak approach (TM-based, most portable)

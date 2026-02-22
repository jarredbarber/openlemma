# Status: Leancubes (Connectedness of Cube Complement)

## Current State
**ESCALATION: Structural gap in escape lemma (3+ attempts, same wall).**

Safe hyperplane: APPROVED + Lean (0 sorrys).
Escape lemma: Phase 2 rewrite (v3) has same gap as all previous versions.

## The Gap

The 2-parameter escape (d1, d2) approach has a structural gap at the final step:

1. d1 = A[1]-S clears all d1-halfline cubes (gap lemma, coord 1). ✅
2. d1-full remaining cubes have d2 half-lines with gap at A[2]-S (gap lemma, coord 2). ✅
3. d1-finite remaining cubes have finite d2 intervals. ✅
4. **GAP: Can the finite d2 intervals completely fill the d2-gap?** No structural argument rules this out.

Concretely: the d2-gap is (max(hi2), min(lo2)), an open interval. Finite d2 intervals [c_i, d_i] could cover it entirely (e.g., one interval [c, d] with c ≤ max(hi2) and d ≥ min(lo2)). No algebraic constraint prevents this.

The gap has persisted through 10+ review rounds across v1-v3. Computational testing shows escape always works (never returns None), but the structural proof is incomplete.

## Possible Resolutions

1. **Multi-segment path**: A→P→T with intermediate point P. More freedom but harder.
2. **Different parameterization**: Single free parameter along a well-chosen direction.
3. **Measure argument**: Bad regions have finite total measure in R^2, so complement is non-empty. But needs care: the feasible region (d1 ∈ G1, d2 ∈ G2) might also have finite measure.
4. **Topological argument**: The complement of finitely many cubes in R^n (n≥3) is connected by a direct topological argument (e.g., Alexander duality, higher connectivity of S^{n-2}).
5. **Constructive escape via n-1 free parameters**: Instead of 2 free params, use all n-1 transverse coords. More parameters → easier to avoid cubes.

## Lemma Pipeline
| Lemma | Python | Review | Lean | Notes |
|-------|--------|--------|------|-------|
| lemma_one_coord_safe | ✅ | APPROVED | ✅ | SafeHyperplane.lean, 0 sorrys |
| lemma_t_range_independent | ✅ | APPROVED | — | leaf lemma |
| lemma_d_interval_bounded | ✅ | APPROVED | — | leaf lemma |
| lemma_gap | ✅ | APPROVED | — | leaf lemma |
| lemma_P3 | ✅ | APPROVED (after fix) | — | t_lo invariant added |
| lemma_escape_exists | ✅ | GAP | — | **step 4 gap: finite intervals filling d2-gap** |
| theorem_complement_connected | — | — | — | depends on escape |

## Code Proofs
| File | Status | Notes |
|------|--------|-------|
| lemma_safe_hyperplane.py | APPROVED + Lean | 0 sorrys |
| lemma_escape_v3.py | Phase 2, GAP at main theorem | Sub-lemmas approved |
| lemma_escape_v2.py | Phase 1, GAP | Computational, tests pass |
| lemma_composition.py | Pending | Depends on escape |

## Activity Log
- 2026-02-21 researcher-1..6, reviewer-1..6: iterations on escape (see git history)
- 2026-02-22 lemma_safe_hyperplane: APPROVED + Lean (0 sorrys)
- 2026-02-22 escape v2 reviewer-7: GAP — epsilon, fixed with GUARD
- 2026-02-22 escape v3 (phase 2 rewrite): sub-lemmas APPROVED, main theorem GAP
- 2026-02-22 **ESCALATION**: same gap after 3+ researcher attempts. Needs human input on proof strategy.

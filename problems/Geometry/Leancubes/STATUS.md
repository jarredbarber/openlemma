# Status: Leancubes (Connectedness of Cube Complement)

## Current State
Incremental pipeline: safe_hyperplane APPROVED + Lean formalized (0 sorrys). Escape lemma under review.

## Proof Strategy
- Union C of 2^n+1 axis-aligned unit cubes is bounded
- For n>=3: escape from A to hyperplane {x_0=S} via segment avoiding all cubes
- 2-parameter target T = (S, S+d1, S+d2, S, ..., S): coords 3+ fixed at S
- Each cube's bad (d1,d2) set bounded in at least one direction -> 2-step sweep always finds good (d1,d2)
- Connect A->T_A->T_B->B via 3 clear segments

## Code Proofs
| File | True | None | Reviewer | Lean |
|------|------|------|----------|------|
| lemma_safe_hyperplane.py | lemma_one_coord_safe | - | APPROVED | SafeHyperplane.lean (0 sorrys) |
| lemma_escape.py | escape_to_safe | - | UNDER REVIEW | - |
| proof_v4.py | all tests | _bad_d_interval loose | GAP | - |
| proof_v5.py | lemma chain | search radius too small | BREAK | - |

## Activity Log
- 2026-02-21 researcher-1: geometry understood, BFS verification for n=3,4, fiber argument
- 2026-02-21 researcher-2: constructive path via perturbation, tests pass
- 2026-02-21 reviewer-1: GAP — 5 issues (sampling, derivation error, universality)
- 2026-02-21 researcher-3: fixed issues, exact intersection, 2D escape lemma
- 2026-02-21 reviewer-2: GAP — proof hygiene (wrong lemma, half-line gap, float)
- 2026-02-21 orchestrator: fixed 4 issues directly
- 2026-02-21 reviewer-3: BREAK — single-segment 2D escape fails for many squares
- 2026-02-21 researcher-4: multi-segment 2D escape (escape_2d.py, proof_v3.py)
- 2026-02-21 reviewer-4: BREAK — cross pattern defeats axis-aligned routing
- 2026-02-21 orchestrator: wrote proof_v4.py (direct R^n diagonal escape, no 2D)
- 2026-02-21 reviewer-5: GAP — testing not proving, infinite fallback, 1D unjustified
- 2026-02-21 researcher-5: proof_v5.py with lemma chain (one-sided bounds)
- 2026-02-21 reviewer-6: BREAK — search radius too small, circular reasoning, 1D bad-d unbounded
- 2026-02-21 orchestrator: designing v6 with 2-parameter sweep (d1 for coord 1, d2 for coord 2)
- 2026-02-22 orchestrator: broke into independent lemmas for incremental pipeline
- 2026-02-22 lemma_safe_hyperplane: APPROVED after 3 review rounds, Lean formalized (0 sorrys)
- 2026-02-22 lemma_escape: submitted to reviewer (2-param sweep, all tests pass)

# Status: Cook-Levin crux-axiom elimination

## Current State
Build green (`lake build botlib.Complexity.CookLevin`, only linter warnings). Starting Bridge 1
(verifier-semantics: `EvalsToInTime ↔ cfgAt-halts`).

## Lemma Pipeline
| Lemma | Python | Review | Lean | Notes |
|-------|--------|--------|------|-------|
| lemma_K_some_implies_S_eq (invariant) | ✅ | APPROVED | ✅ | `kleene_some_implies_stepOrHalt_eq` (Bridge1.lean) |
| lemma_TM2OutputsInTime_to_cfgAt_halt | ✅ | APPROVED | ✅ | `cfgAt_reaches_halt` (Bridge1.lean), 0 sorries |
| bridge2_input_decomp | pending | — | — | not started |
| bridge2_input_decomp | pending | — | — | not started |
| bridge3_adequacy_depth | pending | — | — | not started |
| bridge4_f_polytime | pending | — | — | not started |
| bridge5_L_iff_satisfiable | pending | — | — | depends on 1–4 |
| theorem SAT_is_NP_hard_real | pending | — | — | depends on all bridges |

## Activity Log
- 2026-07-04 orchestrator: verified build green; read handoff + assembly-blocker + workflow docs;
  created Pi project agents `cl-researcher`/`cl-reviewer`/`cl-coder`; created problem dir.
- 2026-07-04 orchestrator: dispatched `cl-researcher` for Bridge 1 (verifier-semantics).
- 2026-07-04 researcher: wrote `exploration/cook-levin/bridge1_verifier_semantics.py` (invariant + forward lemma, adversarial tests).
- 2026-07-04 reviewer (round 1): BREAK on non-determinism (return-type dishonesty) + GAPs (IH not parameter, false-None gate, unlisted iter-unfolding).
- 2026-07-04 researcher (round 2): fixed via `DeterministicStep` wrapper, IH-as-parameter, `lemma_iter_succ`, removed false-None gate.
- 2026-07-04 reviewer (round 2): all 6 units APPROVED; residual framing GAP (non-blocking).
- 2026-07-04 orchestrator: dispatched `cl-coder` to formalize Bridge 1 in Lean (sorry-free target).
- 2026-07-04 coder: formalized Bridge 1 in `Bridge1.lean` (`kleene_some_implies_stepOrHalt_eq`, `cfgAt_reaches_halt`), 0 axioms, 0 sorries, builds green.
- 2026-07-04 orchestrator: independently verified builds green + axiom/sorry inventory unchanged; committing Bridge 1.
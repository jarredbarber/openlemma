# Status: Cook-Levin crux-axiom elimination

## Current State
Build green (`lake build botlib.Complexity.CookLevin`, only linter warnings). Starting Bridge 1
(verifier-semantics: `EvalsToInTime ↔ cfgAt-halts`).

## Lemma Pipeline
| Lemma | Python | Review | Lean | Notes |
|-------|--------|--------|------|-------|
| lemma_K_some_implies_S_eq (invariant) | ✅ | APPROVED | ✅ | `kleene_some_implies_stepOrHalt_eq` (Bridge1.lean) |
| lemma_TM2OutputsInTime_to_cfgAt_halt | ✅ | APPROVED | ✅ | `cfgAt_reaches_halt` (Bridge1.lean), 0 sorries |
| bridge2_initTape_decomp | ✅ | APPROVED | ✅ | `initTape_decomp` (Bridge2.lean) |
| bridge2_certMapped_length | ✅ | APPROVED | ✅ | `certMapped_length` |
| bridge2_certMapped_bool | ✅ | APPROVED | ✅ | `certMapped_bool` + `boolSyms` def |
| bridge2_h_init_connection | ✅ | APPROVED | ✅ | `cfgAt_zero` + `initList_h_init_shape` |
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
- 2026-07-04 researcher (B2): wrote `bridge2_input_decomposition.py` (decomp + length + bool + h_init, no gaps).
- 2026-07-04 reviewer B2 (r1): no BREAK; GAPs (assert-not-prove, latent initList_shape arg bug, misleading Lemma-3 docstring).
- 2026-07-04 researcher (B2 r2): fixed latent bug (concrete arg), docstring scope, threaded sub-lemma deps with propagation.
- 2026-07-04 reviewer B2 (r2): all 4 units APPROVED.
- 2026-07-04 coder: formalized Bridge 2 in `Bridge2.lean` (5 lemmas A-E), 0 axioms, 0 sorries, builds green.
- 2026-07-04 orchestrator: verified builds green + inventory unchanged; committing Bridge 2. (Noted residual: `V.kDecidableEq` vs context `[DecidableEq V.K]` instance agreement - Bridge 5 concern.)
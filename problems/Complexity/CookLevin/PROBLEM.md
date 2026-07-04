# Problem: Cook-Levin — eliminate the crux axiom `SAT_is_NP_hard_citation`

## Goal

Construct `NPHard finEncodingCNF SAT_Language` from real components, eliminating the crux axiom
`botlib/Complexity/CookLevin.lean:43 SAT_is_NP_hard_citation`, with **zero new crux axioms** and
(eventually) zero sorries outside Mathlib. The cert-aware tableau pieces (`CertTableau.lean`,
`CompletenessCert.lean`) and `SAT_in_NP` equivalence are already proven axiom-free.

## Background / authority

- `handoff.md` — current truth, axiom/sorry inventory, five bridges, recommended order.
- `annals/dead-ends/cook-levin-assembly-blocker.md` — authoritative bridge detail.

## The five bridges

1. **Verifier-semantics bridge.** `TM2ComputableInPolyTime` gives `outputsFun : ∀ a,
   TM2OutputsInTime tm (map invFun (encode a)) (some (map invFun (encode (f a)))) (time.eval
   |encode a|)`. Connect this to a `cfgAt` trace that halts with the right output. The core
   lemma is an `EvalsToInTime ↔ cfgAt-halts` correspondence between `(flip bind tm.step)^[t]`
   (Kleene step: `some x → tm.step x`, `none → none`) and `(stepOrHalt V)^[t]` (which uses
   `(V.step cfg).getD cfg`). **Highest-value first target.**
2. **Input-decomposition bridge.** Decompose the paired `(a, cert)` tape into `aInput` and the
   cert-bits region matching `initialConstraintsCert`.
3. **Adequacy / depth preconditions.** Discharge `h_depth`, `h_adequate`, `BoundedReadDepth`
   from the verifier's polytime bound.
4. **Polytime parameterization of `f`.** Fix `tableauFormula_is_polytime`'s statement to the real
   `f` (parameterized over verifier `tm`, time polynomial, `certBound = |enc a|^k`, `boolSyms`).
5. **The `∀ a, L'(a) ↔ Satisfiable (f a)` wrap** using `reduction_sound_cert` (→) and
   `completeness_cert` + `completeness` (←) plus bridges 1–3.

## Hard constraints (from AGENTS.md / handoff)

- Theorem statements immutable; only ADD.
- Never `lake clean`; never rebuild/chmod Mathlib.
- `lake build` green on every commit (sorrys OK, errors not).
- No new crux axioms. Citation axioms only with source. `sorry` temporary + comment.
- Check `annals/dead-ends/` before new approaches.

## Workflow

Code-as-proof (`workflows/code-as-proof/`): researcher drafts Python code proofs → reviewer
adversarially checks (BREAK/GAP/APPROVED) → coder formalizes in Lean 4. The orchestrator (this
session) curates context per subagent and assembles `SAT_is_NP_hard_real` incrementally, keeping
`lake build` green, then replaces the citation and deletes the axiom once all bridge sorries close.

## Key locations

- `botlib/Complexity/Defs.lean`: `InNP`, `PolyTimeReducible`, `NPHard`, `NPComplete`.
- `botlib/Complexity/CookLevin/Completeness.lean`: `stepOrHalt` (21), `cfgAt` (218),
  `cfgAt_succ` (221), `cfgAt_halted_succ` (225), `completeness` (main, near end).
- `botlib/Complexity/CookLevin/CertTableau.lean`: `tableauFormulaCert`,
  `initialConstraintsCert`, `reduction_sound_cert`.
- `botlib/Complexity/CookLevin/CompletenessCert.lean`: `completeness_cert`.
- Mathlib `.lake/packages/mathlib/Mathlib/Computability/TMComputable.lean`: `FinTM2.step` (simp),
  `initList` (109), `haltList` (117), `EvalsTo` (126), `EvalsToInTime` (144),
  `TM2Outputs(InTime)` (162/166), `TM2Computable(InPoly)Time` (196/210).
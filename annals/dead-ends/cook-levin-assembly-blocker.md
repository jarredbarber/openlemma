# Dead-End / Blocker: "Mechanical assembly" of `SAT_is_NP_hard` is NOT possible from current pieces

**Date:** 2026-07-02
**Discovered during:** Step 1 of `handoff.md` (eliminate crux axiom `SAT_is_NP_hard_citation`).
**Status:** ESCALATION — requires maintainer decision on scope. Not a dead-end for the overall
Cook-Levin goal, but a dead-end for the *assumption* that Step 1 is "mostly mechanical gluing."

## Summary

The handoff claims the pieces for `NPHard finEncodingCNF SAT_Language` are "all in place"
(reduction fn `tableauFormula`, `reduction_sound`, `completeness`, `tableauFormula_is_polytime`)
and that assembly is "mostly mechanical gluing." **This is not accurate.** Two structural gaps
prevent assembly. Both were verified by reading the actual theorem statements and constraint
definitions, not just the docs.

## Gap 1 — The certificate is not wired into the tableau (the hard blocker)

`NPHard finEncodingCNF SAT_Language` requires, for every `L' ∈ NP` with verifier `V` on
`(a, b)` (input `a`, certificate `b`, `|b| ≤ |a|^k`), a **poly-time function `f(a)`** with

  `L'(a) ↔ Satisfiable (f a)   ↔   ∃ b (|b| ≤ |a|^k), V accepts (a, b) within poly time`.

The certificate `b` must appear as **free variables** of the single output formula `f(a)` so the
SAT solver "guesses" it. The design doc (`proofs/cook-levin-correctness.md` §"Verifier Tableau")
describes exactly this intent: "variables corresponding to `y` are free (unconstrained)."

**The implementation does not realize this intent:**

- `TableauVar.cert (j : ℕ)` exists (`Tableau.lean:53`) but is referenced **nowhere** except:
  - the inductive definition,
  - its `toSum`/`fromSum` encodings (lines 62, 71),
  - `traceValuation (.cert _) => false` (`Soundness.lean:62`).
- No constraint (`consistencyConstraints`, `initialConstraints`, `transitionConstraints`,
  `framePreservation`, `acceptanceConstraints`) references any `cert` variable.
- `initialConstraints` (`Tableau.lean:116`) fixes **all** stacks: stack `k₀ = inputContents`
  and every other stack `k ≠ k₀` to length 0. So the entire tape is fixed constants; there is
  no free region for a certificate.

Consequence: `reduction_sound` / `completeness` prove a **fixed-input (P-style)** equivalence

  `V halts on the fixed list inputContents within bound ↔ Satisfiable (tableauFormula params inputContents)`

with `BoundedReadDepth` + stack-depth-adequacy side conditions. There is **no existential
certificate quantifier**. This yields a formula `F(input)` satisfiable iff `V` halts on that
specific `input` — i.e. it decides membership for a language in **P**, not NP. Feeding
`inputContents = encode (a, b)` would give `F(a, b)` with `b` *fixed*, not `F(a)` with `b` free.
And feeding `inputContents = encode a` gives `F(a)` satisfiable iff `V` halts on `a` alone —
which is not `L'(a)` (the verifier needs the certificate `b` to run).

To get NP-hardness, the tableau construction must be extended so that:
- the `a` part of the verifier's input tape is fixed (constant literals), and
- the `b` (certificate) part is represented by the free `cert j` variables, with
  `transitionConstraints` referencing `cert (j - |encode a|)` when `V` reads the certificate
  region of its tape,
- plus new soundness/completeness theorems: `Satisfiable (tableauFormulaCert params a) ↔ ∃ b, V accepts (a, b)`.

The existing `reduction_sound` / `completeness` statements are **immutable** (AGENTS.md), so
this must be done by **adding** new definitions and theorems (e.g. `tableauFormulaCert`,
`reduction_sound_cert`, `completeness_cert`), reusing the existing sub-lemmas
(`satisfies_{consistency,initial,transition,frame,acceptance}`) where the cert-aware analog
permits. This is a substantial proof-engineering effort comparable to the existing
soundness/completeness work (~2000 lines), not mechanical gluing.

## Gap 2 — `tableauFormula_is_polytime` is stated for a degenerate constant function

`PolyTime.lean:24`:
```
axiom tableauFormula_is_polytime (V : FinTM2) [...] (params : Params V) :
    TM2ComputableInPolyTime (listEncoding finEncodingNatBool) finEncodingCNF
      (fun (_ : List ℕ) => tableauFormula params [])
```
The function is `fun (_ : List ℕ) => tableauFormula params []` — it **ignores its argument**
and uses **empty input** `[]`. This says "the constant function returning
`tableauFormula params []` is poly-time." It does **not** establish that the actual reduction
map `fun a => tableauFormula params (encode a)` is poly-time. So even Gap 1 aside, this axiom
cannot witness the `TM2ComputableInPolyTime` component of `PolyTimeReducible` for the real
reduction. (It is also a citation axiom, policy-allowed, but useless for assembly as stated.)

## What still holds (no regression)

- `reduction_sound` (`Soundness.lean:898`) and `completeness` (`Completeness.lean:1149`)
  are genuine, 0-axiom, 0-sorry proofs of the **fixed-input** equivalence. The hard invariant
  work (`trace_tracks_full`, `step_tracks_stacks'`, `satisfies_*`) is real and reusable.
- `lake build botlib.Complexity.CookLevin` passes cleanly (1175 jobs, only linter warnings).
- Axiom/sorry inventory matches `handoff.md` exactly; no new regressions.

## Environmental notes (not blockers for Cook-Levin work)

- `lake build botlib` reports failure on two **transitive Mathlib** modules
  (`Mathlib.CategoryTheory.Square`, `Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality`)
  due to `permission denied` writing read-only hash files during Lake replay. These are not
  code errors and are not Complexity dependencies. They are a pre-existing artifact of the
  read-only prebuilt-Mathlib setup (AGENTS.md forbids `chmod`-ing it back). The Complexity
  subtree builds independently and cleanly.
- `botlib/Complexity/Utils.lean:24` has a real unsolved goal but is an **orphan** module
  (imported nowhere), so it does not affect the `botlib` lib build.

## Recommended path forward (needs maintainer input)

This is an escalation per AGENTS.md (crux axiom must be eliminated; cannot add a new crux axiom
to paper over). Options:

1. **Full certificate-aware tableau extension (correct, large).** Implement
   `tableauFormulaCert` + cert-aware soundness/completeness + a real poly-time bound for
   `a ↦ tableauFormulaCert params a`. Use the code-as-proof workflow
   (researcher drafts → reviewer adversarially checks → coder formalizes). Multi-session.
2. **Re-scope the immediate win.** Keep `SAT_is_NP_hard_citation` as an explicit placeholder
   (clearly labeled, not hidden), and instead pursue the *unconditional* sub-pieces that are
   actually reachable now: e.g. fix `tableauFormula_is_polytime`'s statement to cover real
   input (Gap 2), and close the `listEncoding.decode_encode` / `literalSumEncoding` sorrys
   (handoff Steps 2–4). This shrinks the axiom surface without falsely claiming Cook-Levin.
3. **Re-characterize the existing theorem.** Reframe `reduction_sound`/`completeness` as a
   proven "P-completeness / fixed-input tableau" lemma and document honestly that the NP
   certificate step remains, rather than leaving a crux axiom masquerading as assembly.

Do **not** attempt to "assemble" by introducing a new axiom that is the conclusion
`NPHard finEncodingCNF SAT_Language` under another name — that is a crux axiom and is
policy-forbidden.
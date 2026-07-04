# Dead-End / Blocker: `SAT_is_NP_hard` assembly — status after cert-aware tableau work

**Date:** 2026-07-02 (updated)
**Discovered during:** Step 1 of `handoff.md` (eliminate crux axiom `SAT_is_NP_hard_citation`).
**Status:** Gap 1 **CLOSED** (axiom-free). Remaining assembly = trace/semantics bridges + polytime parameterization + `∀a L'(a)↔SAT(f a)` wrap. This is substantial, creative Cook-Levin content — proper code-as-proof (researcher→reviewer→coder) territory, not single-session gluing.

## What changed since the original blocker (Gap 1 CLOSED)

The original blocker was that the certificate was not wired into the tableau. That is now done,
axiom-free, in two new files (statements are ADDITIONS; no existing theorem was modified):

- `botlib/Complexity/CookLevin/CertTableau.lean`:
  - `tableauFormulaCert params aInput certBound boolSyms` — cert-aware tableau formula. The
    `a`-region (stack `k₀` cells `certBound ..` from the bottom) is fixed by `aInput.reverse.zipIdx`;
    the cert-region (cells `0 ..< certBound`) is left free, constrained only by a per-cell
    disjunction clause `[pos (stkElem 0 k₀ j b₀), pos (stkElem 0 k₀ j b₁)]` over the two bool
    symbols `boolSyms` (a free bit per cert cell = a certificate bit).
  - `satisfies_initial_cert` (all 6 parts, incl. the hard a-region `p4` and cert-region `p5`).
  - `reduction_sound_cert` — from a real computation trace `c` (with `h_init`/`h_step`/
    `h_depth`/`h_halt` on `aInput ++ certMapped`), `tableauFormulaCert` is satisfiable.
    0 axioms, 0 sorries. Reuses `satisfies_{consistency,transition,frame,acceptance}` verbatim.
- `botlib/Complexity/CookLevin/CompletenessCert.lean`:
  - helpers `exactlyOne_exists`, `consistency_stkElem_exists`, `sat_components_cert`,
    `cert_not_bool_false` (axiom-free).
  - `completeness_cert`: `Satisfiable (tableauFormulaCert params aInput certBound boolSyms) →
    ∃ cert, cert.length = certBound ∧ (∀ γ ∈ cert, γ ∈ boolSyms) ∧
      Satisfiable (tableauFormula params (aInput ++ cert))`.
    **Fully proven, 0 sorries, 0 crux axioms** (depends only on `propext`, `Classical.choice`,
    `Quot.sound`). Extracts the cert via `Classical.choose`-based total `certF`, splits the
    cell clauses of `initialConstraints (aInput ++ cert)` into cert-region (via `certF_spec`)
    and a-region (via the cert-aware `initialConstraintsCert`'s a-region block), using
    `forall_mem_zipIdx'` + proof-irrelevance of `getElem` values.

So the hard *structural* blocker is gone. `lake build botlib.Complexity.CookLevin` is green.

## Gap 2 — `tableauFormula_is_polytime` still degenerate (unchanged)

`PolyTime.lean:24`:
```
axiom tableauFormula_is_polytime [...] (params : Params V) :
    TM2ComputableInPolyTime (listEncoding finEncodingNatBool) finEncodingCNF
      (fun (_ : List ℕ) => tableauFormula params [])
```
The function ignores its argument and uses empty input `[]`. This is a *citation* axiom
(Arora-Barak 2.10, Sipser 7.37) — **policy-allowed** as a citation, but its **statement** must be
fixed to cover the real reduction map `fun a => tableauFormulaCert params (encode a) …` before it
can witness `PolyTimeReducible`'s polytime component. Fixing the statement (keeping it a citation
axiom) is in-scope and mechanical once the reduction `f` is pinned down (see below).

## Remaining assembly pieces (the real Cook-Levin glue)

To turn the cert-aware pieces into `NPHard finEncodingCNF SAT_Language` (eliminating
`SAT_is_NP_hard_citation`), one must construct, for every `L' ∈ NP` with verifier
`g : α × List Bool → Bool` (with `g_comp : TM2ComputableInPolyTime (pairEncoding ea finEncodingBoolList)
finEncodingBoolBool g`, bound `k`, relation `R`, and `L'(a) ↔ ∃ cert (|cert|=|enc a|^k), R a cert`),
a polytime `f : α → CNF` with `∀ a, L'(a) ↔ Satisfiable (f a)`. Concretely `f a` should be the
cert-aware tableau for the machine computing `g`, on input `(a, cert)`, with `a`-region fixed and
cert-region free. The non-mechanical bridges required:

1. **Verifier semantics bridge.** `TM2ComputableInPolyTime` (Mathlib `TMComputable.lean:210`)
   gives `outputsFun : ∀ a, TM2OutputsInTime tm (map invFun (encode a)) (some (map invFun (encode
   (f a)))) (time.eval |encode a|)`. Need: `g (a, cert) = true ↔ ∃ i ≤ timeBound,
   (cfgAt tm (encode (a,cert)) i).l = none` (the machine halts with output encoding `true`) — i.e.
   connect `TM2OutputsInTime` / `haltList` / `cfgAt` to the Bool output. This is the central
   "V accepts within bound" lemma and is the bulk of the remaining work.

2. **Input decomposition bridge.** `pairEncoding ea finEncodingBoolList` encodes `(a, cert)` as a
   single tape. The cert-aware tableau needs `aInput = encode a` and a cert-region of raw bool
   symbols. Need a lemma decomposing `map invFun (encode (a, cert))` (or `cfgAt`'s initial tape)
   into the `a`-part and the cert-bits part, matching `initialConstraintsCert`'s layout. This
   interacts with how the verifier machine reads its input.

3. **Adequacy / depth preconditions.** `reduction_sound_cert` needs `h_depth` and `completeness`
   needs `h_adequate` (stack depth ≤ `maxStackDepth`), plus `BoundedReadDepth V`. These must be
   discharged from the verifier's polytime bound (the `time` polynomial ⇒ a `maxStackDepth` and
   `timeBound` for which the computation stays within depth). Non-trivial but standard.

4. **Polytime parameterization of `f`.** Fix `tableauFormula_is_polytime`'s statement to the real
   `f` (parameterized over the verifier machine `tm`, its `time` polynomial, and `certBound =
   |encode a|^k`, `boolSyms`). Keep as a citation axiom (allowed) or prove for real (Step 2).
   The `f` must type-check as `TM2ComputableInPolyTime eb finEncodingCNF`.

5. **The `∀ a, L'(a) ↔ Satisfiable (f a)` wrap**, using `reduction_sound_cert` (→) and
   `completeness_cert` + `completeness` (←) plus the bridges above, plus the `cfgAt` trace
   construction (`cfgAt V (aInput ++ certMapped)` with `cfgAt_succ`/`initList` matching
   `reduction_sound_cert`'s `h_init`/`h_step`).

### Mechanical parts already in place (reusable)
- `cfgAt V input t = (stepOrHalt V)^[t] (Turing.initList V input)`, `cfgAt_succ`, `cfgAt_halted_succ`.
- `Turing.initList V input` matches `reduction_sound_cert`'s `h_init` shape
  (`l = some main`, `var = initialState`, `stk k = if k = k₀ then input else []`).
- `stepOrHalt V cfg = (V.step cfg).getD cfg` gives `h_step` from `cfgAt_succ`.
- `finEncodingBoolList` (identity encoding for `List Bool`) ensures every cert bit-string is valid.

## Why this is not "mechanical gluing"

Bridges 1–3 are genuine Cook-Levin content (verifier computation ↔ tableau trace ↔ accept
semantics), comparable in size to the existing soundness/completeness work. Per `AGENTS.md`, this
creative proof work should go through the **code-as-proof workflow**
(researcher drafts → reviewer adversarially checks → coder formalizes), multi-session. The
orchestrator should dispatch the researcher with the context: cert-aware pieces (above),
`InNP`/`NPHard`/`PolyTimeReducible`/`TM2ComputableInPolyTime` definitions, and the five bridges.

## Do NOT
- Introduce a new axiom whose conclusion is `NPHard finEncodingCNF SAT_Language` (crux axiom,
  policy-forbidden).
- Modify existing theorem statements (`reduction_sound`, `completeness`, etc. are immutable).
- `lake clean` / rebuild Mathlib.

## Other remaining items (independent of the crux axiom; lower priority)
- `listEncoding.decode_encode` (`Encodings.lean:76`) — one sorry in the cons case. The key lemma
  `List.splitOnP_first` is available, but `FinEncoding` projection elaboration
  (`(listEncoding ea).Γ` not reducing to `Option ea.Γ` in `cons` positions) makes the cons case
  brittle. Deferred; self-contained; not on the Cook-Levin critical path.
- `SAT_in_NP` — 1 sorry remains: the poly-time verifier (`hg_comp`). The
  Satisfiable↔∃cert equivalence is FULLY PROVEN (cert construction via `findPos_mem` +
  `evalCNF_eq_of_vars_eq`; encoding-length bound `|dedup| ≤ |enc φ|` via `sum_map_le` +
  `length_le_sum_of_one_le`). Only the polytime verifier (`TM2ComputableInPolyTime ...
  SAT_VerifierBits`) is still sorry'd — citation-axiom territory. Step 6 (mostly done).
- `polyTimeFst_empty_alphabet` (`PolyTimeFst.lean:284`) — axiom for the empty-alphabet edge case.
- `botlib/Complexity/Utils.lean:24` — unsolved goal in an orphan module (imported nowhere).
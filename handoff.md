# Handoff: OpenLemma Cook-Levin — eliminate the crux axiom

You are continuing the formalization of the **Cook-Levin theorem** in Lean 4. The single
headline goal: **eliminate the crux axiom `SAT_is_NP_hard_citation`** by constructing
`NPHard finEncodingCNF SAT_Language` from real components, with **zero new crux axioms**
and (eventually) zero sorries outside Mathlib. Everything below is the current truth as of
the last green commit — read it before touching code.

## Environment (already set up — do not redo)

- Lean `4.27.0`, Lake `5.0.0-src`, elan `4.1.2`. Toolchain pinned via `lean-toolchain` (`leanprover/lean4:v4.27.0`).
- Mathlib `v4.27.0` (rev `a3a10db0e9d66acbebf76c5e6a135066525ac900`) is installed **prebuilt**.
  - `.lake/packages/mathlib/` has sources + ~7,523 prebuilt `.olean` files pulled via `lake exe cache get`.
  - **Mathlib is locked read-only** (`chmod -R a-w`). Do NOT chmod it back. Do NOT run `lake clean`
    (corrupts the shared cache — forbidden by `AGENTS.md`). Do NOT run `lake update`.
  - Never rebuild Mathlib from source. Always rely on the prebuilt oleans.
- Verify the build first thing:
  ```bash
  lake build botlib.Complexity.CookLevin   # currently green: ~1175 jobs, only linter warnings
  ```

## What is now PROVED (axiom-free) — the foundation is done

The hard mathematical parts are complete and depend only on `propext`, `Classical.choice`,
`Quot.sound` (no crux axioms, no sorries):

- `reduction_sound` (`CookLevin/Soundness.lean:898`): a real TM2 computation trace (with
  `h_init`/`h_step`/`h_depth`/`h_halt`/`BoundedReadDepth`) ⇒ `tableauFormula params input` satisfiable.
- `completeness` (`CookLevin/Completeness.lean`, main `theorem completeness` near end):
  `Satisfiable (tableauFormula params input)` (with `BoundedReadDepth` + adequacy) ⇒
  `∃ i ≤ timeBound, (cfgAt V input i).l = none`.
- **Cert-aware tableau — Gap 1 CLOSED (axiom-free), the new content this phase:**
  - `CookLevin/CertTableau.lean` (214 lines): `tableauFormulaCert params aInput certBound
    boolSyms` (a-region fixed to `aInput.reverse.zipIdx`; cert-region cells `0..<certBound`
    free, constrained only by a per-cell disjunction `[pos (stkElem 0 k₀ j b₀),
    pos (stkElem 0 k₀ j b₁)]` over the two bool symbols), `satisfies_initial_cert`
    (all 6 parts incl. the hard a-region `p4` + cert-region `p5`), and
    `reduction_sound_cert` (reuses `satisfies_{consistency,transition,frame,acceptance}`).
  - `CookLevin/CompletenessCert.lean` (279 lines): helpers `exactlyOne_exists`,
    `consistency_stkElem_exists`, `sat_components_cert`, `cert_not_bool_false`, and
    **`completeness_cert`** — fully proven: `Satisfiable (tableauFormulaCert params aInput
    certBound boolSyms) → ∃ cert, cert.length = certBound ∧ (∀ γ ∈ cert, γ ∈ boolSyms) ∧
    Satisfiable (tableauFormula params (aInput ++ cert))`. Extracts the cert via a
    `Classical.choose`-based total `certF`, splits the cell clauses of
    `initialConstraints (aInput ++ cert)` into cert-region (via `certF_spec`) and a-region
    (via the cert-aware `initialConstraintsCert` block), using `forall_mem_zipIdx'`.
- **`SAT_in_NP` equivalence fully proven** (`SAT.lean`): the
  `Satisfiable φ ↔ ∃ cert (|cert|=|enc φ|) ∧ evalCNF (assignmentFromBits cert φ) φ = true`
  direction is real (cert = `φ.vars.dedup.map σ` padded to `|enc φ|`; agreement via the new
  `findPos_mem` helper + `evalCNF_eq_of_vars_eq`; the encoding-length bound `|dedup| ≤ |enc φ|`
  via the new `sum_map_le` helper + `List.length_le_sum_of_one_le` + `listEncoding_length`).
- `InNP` was refined to **raw-bit certificates**: identity encoding `finEncodingBoolList`
  (`encode = id`, `decode = some`), exact-length bound `cert.length = |enc a|^k`, verifier is
  `Nonempty (TM2ComputableInPolyTime (pairEncoding ea finEncodingBoolList) finEncodingBoolBool g)`.
  `P ⊆ NP` re-proved for the new shape. `literalSumEncoding` made real (eliminates 2 old sorries).

## Current axiom / sorry inventory (exact, build-green)

```
botlib/Complexity/CookLevin.lean:43          axiom SAT_is_NP_hard_citation : NPHard finEncodingCNF SAT_Language   # CRUX — the target
botlib/Complexity/CookLevin/PolyTime.lean:24 axiom tableauFormula_is_polytime …                              # citation (allowed) — degenerate stmt
botlib/Complexity/PolyTimeFst.lean:284       axiom polyTimeFst_empty_alphabet …                              # citation (allowed)
botlib/Complexity/SAT.lean:304               … SAT_VerifierBits … := sorry                                  # hg_comp: polytime verifier (Step 6 remnant)
botlib/Complexity/Encodings.lean:93          sorry                                                            # listEncoding.decode_encode cons (latent, not consumed)
```
No other sorries/axioms in `botlib/Complexity/` (the `Utils.lean:24` unsolved goal is in an
orphan module imported nowhere). **The crux axiom is the only policy-violating item.**

## The headline task: eliminate `SAT_is_NP_hard_citation`

`NPHard finEncodingCNF SAT_Language` (Defs.lean) is:
```
∀ {β} (eb : FinEncoding β) (L' : Language β), InNP eb L' → PolyTimeReducible eb finEncodingCNF L' SAT_Language
```
`PolyTimeReducible eb ea L' L = ∃ (f : β → α) (_comp : TM2ComputableInPolyTime eb ea f), ∀ a, L' a ↔ L (f a)`.

`InNP eb L'` destructures to:
```
∃ (R : β → List Bool → Prop) (k : ℕ) (g : β × List Bool → Bool)
  (g_comp : Nonempty (TM2ComputableInPolyTime (pairEncoding eb finEncodingBoolList) finEncodingBoolBool g)),
  (∀ a cert, R a cert ↔ g (a, cert) = true) ∧
  ∀ a, L' a ↔ ∃ cert, cert.length = (eb.encode a).length ^ k ∧ R a cert
```

So for each `InNP eb L'` with verifier `g` and `g_comp`, you must build a polytime
`f : β → CNF` with `∀ a, L' a ↔ SAT_Language (f a)`, where `f a` is the cert-aware tableau
for the machine computing `g`, on input `(a, cert)`, with the `a`-region fixed to
`encode a` and the cert-region free. This requires **five bridges** (see
`annals/dead-ends/cook-levin-assembly-blocker.md` for full detail):

1. **Verifier-semantics bridge** (the bulk). `TM2ComputableInPolyTime` (Mathlib
   `Computability/TMComputable.lean`) gives `outputsFun : ∀ a, TM2OutputsInTime tm
   (map inputAlphabet.invFun (encode a)) (some (map outputAlphabet.invFun (encode (g a))))
   (time.eval |encode a|)`. Connect this to a `cfgAt` trace that halts accepting.
   **Key facts (verified this session):**
   - `EvalsTo`/`EvalsToInTime` iterate `flip bind tm.step` from `some (initList tm l)` — i.e.
     `(flip bind tm.step)^[steps] (some init) = b` is the "Kleene step" (`some x → tm.step x`,
     `none → none`). Concretely `(EvalsTo.refl f a).evals_in_steps : (flip bind f)^[_] (some a) = some a`.
   - `cfgAt V input t = (stepOrHalt V)^[t] (Turing.initList V input)` with
     `stepOrHalt V cfg = (V.step cfg).getD cfg` (Completeness.lean:21,218). While running,
     `stepOrHalt` extracts the `some`; once `V.step cfg = none` (halted) it stays at `cfg`.
   - So the needed lemma is essentially: `EvalsToInTime V.step init (some (haltList V out)) m ↔
     ∃ t ≤ m, cfgAt V input t = haltList V out` — a `flip bind`↔`stepOrHalt` correspondence.
     This is a **real lemma, not `rfl`**; proving it cleanly is the central remaining proof.
   - `initList V input = {l := some V.main, var := V.initialState, stk := fun k => if k = k₀
     then input else []}` — matches `reduction_sound`/`reduction_sound_cert`'s `h_init` shape.
2. **Input-decomposition bridge.** `pairEncoding eb finEncodingBoolList` encodes `(a, cert)`
   as one tape. Decompose `map invFun (encode (a, cert))` (or the `cfgAt` initial tape) into
   the `a`-part (`= aInput`) and the cert-bits part, matching `initialConstraintsCert`'s layout
   (cert cells `0..<certBound`, a-region `certBound..` from the bottom, `certBound = |enc a|^k`).
3. **Adequacy / depth preconditions.** `reduction_sound_cert` needs `h_depth` and
   `completeness` needs `h_adequate` (`∀ t' k, t' ≤ timeBound → (cfgAt V input t').stk k |>.length
   ≤ maxStackDepth`) plus `BoundedReadDepth V`. Discharge these from the verifier's polytime
   bound (the `time` polynomial ⇒ a `maxStackDepth` + `timeBound` for which the computation
   stays within depth). Standard but non-trivial.
4. **Polytime parameterization of `f`.** Fix `tableauFormula_is_polytime`'s statement to the
   real `f` (parameterized over the verifier `tm`, its `time` polynomial, `certBound = |enc a|^k`,
   `boolSyms`). Keep as a citation axiom (allowed) or prove for real (Step 2 below). The `f`
   must type-check as `TM2ComputableInPolyTime eb finEncodingCNF`.
5. **The `∀ a, L' a ↔ SAT_Language (f a)` wrap.** Using `reduction_sound_cert` (→) and
   `completeness_cert` + `completeness` (←) plus bridges 1–3, plus the `cfgAt` trace
   construction (`cfgAt V (aInput ++ certMapped)` via `cfgAt_succ`/`initList`) matching
   `reduction_sound_cert`'s `h_init`/`h_step`.

**This is substantial, creative Cook-Levin content — not mechanical gluing.** Per `AGENTS.md`,
do this via the **code-as-proof workflow** (`workflows/code-as-proof/`):
researcher drafts each bridge as a Python code-proof → reviewer adversarially checks → coder
formalizes. Dispatch the researcher with curated context: the cert-aware pieces
(`CertTableau.lean`, `CompletenessCert.lean`), `InNP`/`NPHard`/`PolyTimeReducible`/
`TM2ComputableInPolyTime` defs, `cfgAt`/`EvalsTo`/`initList`, and the five bridges above.
**Bridge 1 is the highest-value first target.**

### Suggested concrete scaffold (do this only if you can keep it building)
Rather than one blanket `sorry` on `NPHard`, state each bridge as a **separately-typed lemma**
with a precise type and `sorry`, then assemble `theorem SAT_is_NP_hard_real : NPHard
finEncodingCNF SAT_Language` calling them. Keep the existing `SAT_is_NP_hard_citation` axiom in
place until **all** bridge sorries close, then replace `SAT_is_NP_hard := SAT_is_NP_hard_real`
and delete the axiom. Do NOT create a theorem whose only body is `sorry` (that is a crux axiom
in disguise). Getting the bridge types exactly right is itself the hard part — if a scaffold
won't build, back out (`git checkout`) rather than commit a mis-typed stub.

## Independent lower-priority items (not on the critical path)

- **`SAT_in_NP.hg_comp`** (`SAT.lean:304`): the polytime verifier `TM2ComputableInPolyTime
  (pairEncoding finEncodingCNF finEncodingBoolList) finEncodingBoolBool SAT_VerifierBits`.
  Citation-axiom territory (SAT verification is polytime — standard). Needed for
  `CookLevin : NPComplete` to be fully unconditional on the `SAT ∈ NP` side, but does NOT block
  the crux-axiom elimination (which is about the `NPHard` side).
- **`tableauFormula_is_polytime`** (`CookLevin/PolyTime.lean:24`): currently a degenerate
  citation axiom (constant `fun _ => tableauFormula params []`). Its statement must be fixed to
  the real `f` for Bridge 4, then optionally proven (Step 2). Infrastructure: `TM2PolyTimeComp.lean`
  (axiom-free polytime composition, `TM2ComputableInPolyTime.comp`).
- **`polyTimeFst_empty_alphabet`** (`PolyTimeFst.lean:284`): citation axiom for the empty-alphabet
  edge case of `Prod.fst` polytime.
- **`listEncoding.decode_encode`** (`Encodings.lean:93`): one sorry in the cons case. The key
  lemma `List.splitOnP_first` is available (in `Mathlib.Algebra.BigOperators.Group.List.Basic`
  and `Mathlib.Data.List.SplitOn`), but the `(listEncoding ea).Γ` field projection does not
  reduce to `Option ea.Γ` in the elaborator, so `BEq (listEncoding ea).Γ` is not synthesized and
  `none`/`some` fail to unify. **Latent — no consumer references it.** Approach: `change` the
  whole `decode`/`encode` expression to `Option ea.Γ` up to defeq before applying `splitOnP_first`.
- **`botlib/Complexity/Utils.lean:24`**: unsolved goal in an orphan module imported nowhere.
  Either fix or delete.

## Recommended order of work

1. **Re-verify build** (Step 0): `lake build botlib.Complexity.CookLevin` — confirm green.
2. **Bridge 1 (verifier semantics)** via code-as-proof — the highest-value, most foundational
   piece. Lands a typed `EvalsToInTime ↔ cfgAt-halts` lemma reusable by the whole assembly.
3. **Bridges 2–5**, ideally with reviewer checkpoints, building the `SAT_is_NP_hard_real`
   scaffold incrementally so `lake build` stays green on every commit.
4. **Eliminate the crux axiom**: once all bridge sorries close, replace `SAT_is_NP_hard` and
   delete `SAT_is_NP_hard_citation`.
5. **`hg_comp`** + `tableauFormula_is_polytime` (real) → `CookLevin : NPComplete` unconditional.
6. **Cleanup**: `listEncoding.decode_encode`, `polyTimeFst_empty_alphabet`, `Utils.lean`, docs sync.

## Key definitions / locations (orientation)

- `Defs.lean`: `InNP`, `PolyTimeReducible`, `NPHard`, `NPComplete`, `PolyTimeComp`.
- `Encodings.lean`: `finEncodingBoolList` (identity for `List Bool`), `listEncoding`,
  `pairEncoding`, `sumEncoding`, `listEncoding_length`, `Option.sequence`.
- `SAT.lean`: `finEncodingClause`, `finEncodingCNF`, `finEncodingLiteral`, `findPos`,
  `findPos_mem`, `sum_map_le`, `assignmentFromBits`, `SAT_VerifierBits`, `SAT_in_NP`, `SAT_Language`.
- `CookLevin/Tableau.lean`: `Params V` (`timeBound`, `maxStackDepth`), `tableauFormula`,
  `consistencyConstraints`, `initialConstraints`, `transitionClausesAt`, `TableauVar`.
- `CookLevin/Completeness.lean`: `stepOrHalt` (21), `cfgAt` (218), `cfgAt_succ`,
  `cfgAt_halted_succ`, `completeness` (main, near end), `BoundedReadDepth`.
- `CookLevin/Soundness.lean`: `reduction_sound` (898) + all `satisfies_*` sub-lemmas.
- `CookLevin/CertTableau.lean`: `tableauFormulaCert`, `initialConstraintsCert`,
  `satisfies_initial_cert`, `reduction_sound_cert` (188).
- `CookLevin/CompletenessCert.lean`: `completeness_cert` (166) + cert-extraction helpers.
- `CookLevin/PolyTime.lean`: `tableauFormula_is_polytime` (24, degenerate citation axiom).
- Mathlib `Computability/TMComputable.lean`: `FinTM2.step`, `initList` (109), `haltList` (117),
  `EvalsTo`/`EvalsToInTime` (126/144), `TM2Outputs(InTime)` (162/166), `TM2Computable(InPoly)Time`
  (196/210), `outputsFun`, `TM2ComputableInPolyTime.toTM2ComputableInTime`.
- `annals/dead-ends/cook-levin-assembly-blocker.md`: the authoritative detailed bridge doc —
  **read it fully before starting**. (Note: its "SAT_in_NP — 2 sorries" line is now stale;
  equivalence is proven, only `hg_comp` remains.)

## Hard constraints (from AGENTS.md)

- **Theorem statements are immutable.** Never modify them. Only ADD new definitions/theorems.
- **Never run `lake clean`.** It corrupts the shared Mathlib cache. Never rebuild/chmod Mathlib.
- **`lake build` must pass on every commit.** Sorrys OK; errors are not. Commit green only.
- **No new axioms without maintainer approval.** Citation axioms only with verified source.
  **Crux axioms (conclusion == theorem statement) are forbidden** — escalate, do not add.
  Never paper over a gap with an axiom whose conclusion is `NPHard finEncodingCNF SAT_Language`.
- **`Sorry` is temporary only** — must carry a comment explaining what's needed. Never ship a
  bare `sorry` as a substitute for the crux axiom.
- Check `annals/dead-ends/` before starting an approach. Don't repeat known failures.
- One task `in_progress` at a time in the todo list; mark completed immediately when done.
- Never mark a task completed while tests/build fail or the implementation is partial.

## Quick orientation commands

```bash
lake build botlib.Complexity.CookLevin               # verify reduction builds (green)
rg -n "axiom |sorry" botlib/Complexity/ | grep -v ROADMAP   # current gaps
git log --oneline -14                                  # this phase's commits
cat annals/dead-ends/cook-levin-assembly-blocker.md    # authoritative bridge detail
grep -n "def InNP\|def NPHard\|def PolyTimeReducible" botlib/Complexity/Defs.lean
```
# Handoff: OpenLemma Cook-Levin Formalization

## Environment (already set up — do not redo)

- Lean `4.27.0`, Lake `5.0.0-src`, elan `4.1.2`. Toolchain pinned via `lean-toolchain` (`leanprover/lean4:v4.27.0`).
- Mathlib `v4.27.0` (rev `a3a10db0e9d66acbebf76c5e6a135066525ac900`) is installed **prebuilt**.
  - `.lake/packages/mathlib/` contains sources + 7,523 prebuilt `.olean` files (6.0 GB) pulled from the Azure cache via `lake exe cache get`.
  - **Mathlib is locked read-only** (`chmod -R a-w`). Do not chmod it back. Do not run `lake clean` (corrupts the shared cache — forbidden by `AGENTS.md`). Do not run `lake update` unless you intend to re-pull deps; it will fail against the read-only mathlib dir, which is the desired safeguard.
  - Rebuilding Mathlib from source is forbidden by the user. Always rely on the prebuilt oleans.
- A smoke build already passed: `lake build botlib.Complexity.Defs` → success (1166 jobs), no errors, only linter warnings.

## Project layout that matters here

- `botlib/Complexity/CookLevin/{Tableau,Correctness,Soundness,Completeness,PolyTime}.lean` — the reduction.
- `botlib/Complexity/CookLevin.lean` — hub that assembles `CookLevin : NPComplete`.
- `botlib/Complexity/{Defs,SAT,Encodings,PolyTimeFst,TM2PolyTimeComp}.lean` — supporting definitions/encodings.
- `botlib/Complexity/ROADMAP.md` — per-phase status (last stats dated 2026-02-12).
- `artifacts/cook-levin-trace-citation.md` — citation verification for the trace axiom.
- Workflow docs: `workflows/code-as-proof/` (researcher→reviewer→coder pipeline). Agent prompts: `.claude/agents/`.

## What is genuinely proved (axiom-free)

- `reduction_sound` (`CookLevin/Soundness.lean:898`): TM accepts within bound ⇒ `tableauFormula` satisfiable. 0 axioms, 0 sorrys. All sub-lemmas (`satisfies_{consistency,initial,transition,frame,acceptance}`) closed.
- `completeness` (`CookLevin/Completeness.lean`, main theorem at end of file): `tableauFormula` satisfiable ⇒ TM halts within bound. 0 axioms, 0 sorrys. Key cruxes `step_tracks_running`, `step_tracks_stacks'` (~400 lines), `trace_base_stacks'`, and the full invariant `trace_tracks_full` are all proved.
- `stepAux_soundness` / `stepAux_preservation_elem` (`Correctness.lean`): axiom-free by structural induction.
- `Tableau.lean` construction: 0 sorrys.

These are the hard mathematical parts and they are done.

## What remains (the gap to an unconditional Cook-Levin)

Listed by severity. Per `AGENTS.md` axiom policy: **citation axioms** (with verified source) are allowed; **crux axioms** (conclusion == theorem statement) are NOT allowed and must be escalated/eliminated.

1. **`SAT_is_NP_hard_citation`** (`CookLevin.lean:43`) — **CRUX AXIOM, policy-violating.** Its statement *is* `NPHard finEncodingCNF SAT_Language`, and `SAT_is_NP_hard` is defined as `:= SAT_is_NP_hard_citation`. This is the final assembly and must be eliminated by constructing `NPHard` from: the reduction function, `reduction_sound`, `completeness`, and `tableauFormula_is_polytime`. This is the headline remaining task.

2. **`tableauFormula_is_polytime`** (`CookLevin/PolyTime.lean:24`) — citation axiom (Arora-Barak 2.10, Sipser 7.37). Policy-allowed as a citation, but blocks item 1 from being fully unconditional. Either (a) keep as citation and assemble item 1 on top of it, or (b) prove it for real.

3. **`SAT_Verifier_polytime`** and **`cert_encoding_le_cube`** (`SAT.lean:247,260`) — citation axioms underpinning `SAT_in_NP`. Needed for the `NPComplete = ⟨SAT_in_NP, SAT_is_NP_hard⟩` assembly to be unconditional.

4. **`polyTimeFst_empty_alphabet`** (`PolyTimeFst.lean:284`) — axiom for the empty-alphabet edge case of `Prod.fst` poly-time.

5. **`listEncoding.decode_encode`** (`Encodings.lean:76`) — one `sorry` in the cons case (deferred "due to brittle list-splitting lemmas"). Affects downstream list encodings.

6. **`literalSumEncoding`** + its `DecidableEq`** (`SAT.lean:137,139`) — two `sorry`s. File notes these are **not** used by the Cook-Levin proofs (which use `Encodable`). Low priority; scaffolding debt.

## Recommended next steps (in order)

### Step 0 — Re-verify the build end-to-end
The "0 sorrys / 0 axioms" claims in `ROADMAP.md` are dated 2026-02-12 and have not been type-checked since Mathlib was restored this session. Before any new work:
```bash
lake build botlib.Complexity.CookLevin      # the reduction itself
lake build botlib.Complexity                # the whole Complexity lib
lake build                                  # full project (botlib + problems)
```
Confirm zero errors. Grep for regressions:
```bash
rg -n "axiom |sorry|admit" botlib/Complexity/
```
If anything broke against the pinned Mathlib, fix that first — do not add new proof work on top of a red build.

### Step 1 — Eliminate the crux assembly axiom (highest value)
Replace `SAT_is_NP_hard_citation` in `botlib/Complexity/CookLevin.lean` with a real construction of `NPHard finEncodingCNF SAT_Language`. The pieces are all in place:
- reduction function: `tableauFormula params` (Tableau.lean)
- soundness: `reduction_sound`
- completeness: `completeness`
- poly-time: `tableauFormula_is_polytime` (keep as citation axiom for now — allowed)

`NPHard` is defined in `Defs.lean`; check the exact constructor shape. This single change converts `CookLevin` from "crux-axiom-wrapped" to "assembled from components with one allowed citation axiom (poly-time)." That is a major policy milestone.

Use the code-as-proof workflow if helpful: researcher drafts the assembly argument as a Python code-proof, reviewer adversarially checks it, coder formalizes. But this is mostly mechanical gluing — may not need the full pipeline.

### Step 2 — Prove `tableauFormula_is_polytime` for real
This is the last non-crux axiom on the reduction side. Show `tableauFormula params` is `TM2ComputableInPolyTime` by bounding the formula size `O(T·(K·S + |Λ|))` and giving the TM2 construction. `TM2PolyTimeComp.lean` (1431 lines, axiom-free composition) is the infrastructure for this. After this, item 1's assembly becomes fully unconditional on the reduction side.

### Step 3 — Close SAT ∈ NP citation axioms
Prove `SAT_Verifier_polytime` and `cert_encoding_le_cube` in `SAT.lean` so `SAT_in_NP` is unconditional. Combined with Steps 1–2, this makes `CookLevin : NPComplete` depend on zero axioms.

### Step 4 — Clean up the encoding sorrys
- `listEncoding.decode_encode` (Encodings.lean:76): prove the cons case using `List.splitOn` lemmas.
- `literalSumEncoding` (SAT.lean:137,139): implement a real `FinEncoding (Sum ℕ ℕ)` (the file notes `sumEncoding` is missing from this Mathlib version — check whether it has since appeared, or build it from `Encodable` instances).

### Step 5 — Sync docs
Update `botlib/Complexity/ROADMAP.md` "Current Stats" with the new date, axiom/sorry counts, and mark the completed items. Commit per the `lake build must pass on every commit` rule.

## Hard constraints (from AGENTS.md)

- Theorem statements are immutable. Never modify them.
- Never run `lake clean`. Never rebuild Mathlib.
- `lake build` must pass on every commit. Sorrys OK; errors not.
- No new axioms without maintainer approval. Citation axioms only with verification. Crux axioms: escalate, do not add.
- Check `annals/dead-ends/` before starting an approach (currently empty except README).
- One task in_progress at a time in the todo list; mark completed immediately when done.

## Quick orientation commands

```bash
lake build botlib.Complexity.CookLevin        # verify reduction builds
rg -n "axiom |sorry|admit" botlib/Complexity/ # find remaining gaps
git log --oneline -- botlib/Complexity/CookLevin/ | head   # proof history
cat botlib/Complexity/ROADMAP.md              # phase tracker
```
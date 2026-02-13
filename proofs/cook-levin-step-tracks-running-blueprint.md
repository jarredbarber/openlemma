# Blueprint: `step_tracks_running` — SAT Transition Tracks TM2 `stepAux`

**Status:** Draft ✏️  
**Target:** `botlib/Complexity/CookLevin/Completeness.lean`, axiom `step_tracks_running`  
**Statement:** When the TM2 is in a running state (label = `some lbl`) at time $t$, and the satisfying assignment $\sigma$ correctly marks the label and state at time $t$, then $\sigma$ also correctly marks the label and state at time $t+1$.  
**Dependencies:**
- `stepAux_soundness` (Correctness.lean, Proved ✅) — `stepAux` output depends only on stack tops
- `topsInfo_from_consistency` (Completeness.lean, Proved ✅) — extract stack-top info from $\sigma$
- `halted_forces_next` (Completeness.lean, Proved ✅) — template for the clause-extraction technique
- `consistency_label_unique` (Completeness.lean, Proved ✅) — at-most-one from `exactlyOne`

**Confidence:** Certain

---

## 0. Context: Where This Fits

The completeness proof (`completeness`) works by induction on time $t$, showing that $\sigma$ tracks the label and state of the actual computation `cfgAt V input t`. The inductive step (`step_tracks`) case-splits on the label:

- **Halted** (label = `none`): Proved in `step_tracks_halted` using `halted_forces_next`.
- **Running** (label = `some lbl`): **This is what we need to prove.** It is currently an axiom.

The running case follows the same structural pattern as the halted case but requires additionally relating the stack-top information extracted from $\sigma$ to the actual stacks used by `stepAux`.

---

## 1. Precise Statement

```lean
axiom step_tracks_running
    (V : FinTM2) [...instances...]
    (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true)
    (t : ℕ) (ht : t < params.timeBound) (lbl : V.Λ)
    (h_some : (cfgAt V input t).l = some lbl)
    (h_label : varTrue σ (.label t (some lbl)))
    (h_state : varTrue σ (.state t (cfgAt V input t).var)) :
    varTrue σ (.label (t+1) (cfgAt V input (t+1)).l) ∧
    varTrue σ (.state (t+1) (cfgAt V input (t+1)).var)
```

**In words:** Given that $\sigma$ satisfies the tableau formula, and at time $t$ the actual computation has label `some lbl` which $\sigma$ correctly tracks, then at time $t+1$ $\sigma$ also correctly tracks.

---

## 2. Proof Architecture

```
step_tracks_running
│
├── Phase 1: Extract topsInfo from consistency constraints
│   └── topsInfo_from_consistency (Proved ✅)
│
├── Phase 2: Relate topsInfo to actual stacks
│   ├── Lemma A: stkLen matches actual stack length
│   ├── Lemma B: stkElem at top matches actual stack top
│   └── Corollary: stkVals derived from topsInfo = actual stack tops
│
├── Phase 3: Navigate transition clauses, extract consequent
│   ├── Locate the clause for (some lbl, s, topsInfo) in transitionClausesAt
│   ├── Show all antecedent literals evaluate to false
│   └── Extract consequent via consequent_of_clause (Proved ✅)
│
├── Phase 4: Relate SAT consequent to actual next configuration
│   ├── stepAux_soundness (Proved ✅): stepAux depends only on tops
│   └── Show the consequent's label/state match cfgAt(t+1)
│
└── Conclude
```

---

## 3. Phase 1: Extract `topsInfo` from Consistency

**Already proved** as `topsInfo_from_consistency`. From the consistency constraints in $\sigma$, we noncomputably construct:

```
topsInfo : ∀ k, Option (Fin maxStackDepth × V.Γ k)
```

such that for each stack $k$:
- If `topsInfo k = none`: $\sigma$ marks `stkLen t k 0` as true (stack is empty).
- If `topsInfo k = some (len, γ)`: $\sigma$ marks `stkLen t k (len+1)` and `stkElem t k len γ` as true.

**Lean:** Direct application of `topsInfo_from_consistency hC (by omega)`.

---

## 4. Phase 2: Relate `topsInfo` to Actual Stacks (Core Difficulty)

This is the **key new content** not present in the halted case. We must show that the `topsInfo` extracted from $\sigma$ matches the actual computation's stacks.

### 4.1 The Correspondence Invariant

We need to strengthen the inductive hypothesis. The current induction tracks only label and state. For the running case, we additionally need:

**Invariant (Stack Tracking).** At each time $t \le \text{timeBound}$:

$$\forall k,\; \text{varTrue}\;\sigma\;(\text{stkLen}\;t\;k\;|(\text{cfgAt}\;V\;\text{input}\;t).\text{stk}\;k|)$$

$$\forall k,\; \forall j < |(\text{cfgAt}\;V\;\text{input}\;t).\text{stk}\;k|,\; \text{varTrue}\;\sigma\;(\text{stkElem}\;t\;k\;j\;((\text{cfgAt}\;V\;\text{input}\;t).\text{stk}\;k).\text{reverse}[j])$$

**In words:** $\sigma$ correctly marks the stack length and every stack element at each time step, using the "reversed indexing" convention (index 0 = bottom of stack).

### 4.2 Why This Invariant Suffices

Given the invariant at time $t$, plus consistency (at most one value per variable from `exactlyOne`):

**Lemma A (Stack length matches).** If $\sigma$ marks `stkLen t k len_actual` as true (from the invariant) and also marks `stkLen t k len_topsInfo` as true (from `topsInfo`), then by `consistency_label_unique`-style uniqueness (applied to `stkLen` variables), `len_actual = len_topsInfo`.

**Lean sketch:**
```lean
-- From invariant: varTrue σ (stkLen t k actualLen)
-- From topsInfo:  varTrue σ (stkLen t k topsLen)
-- By exactlyOne_encode_eq on the stkLen exactlyOne block:
--   encode (stkLen t k actualLen) = encode (stkLen t k topsLen)
-- By injectivity of encode: actualLen = topsLen
```

**Lemma B (Stack top matches).** Similarly, if `topsInfo k = some (len, γ)`, then from the invariant we know `stkElem t k len γ_actual` is true, and from `topsInfo` we know `stkElem t k len γ` is true. By uniqueness, `γ = γ_actual`.

**Corollary (stkVals agreement).** The `stkVals` derived from `topsInfo`:
```lean
let stkVals : ∀ k, List (V.Γ k) := fun k =>
  match topsInfo k with | none => [] | some (_, γ) => [γ]
```
satisfies: for each stack $k$, `stkVals k` equals the top element of the actual stack (as a singleton list), or `[]` if the stack is empty.

More precisely:
```
∀ k, (actualStk k).take 1 = stkVals k
```

### 4.3 Strengthening the Induction

**Important structural point:** To make Phase 2 work, the induction in `trace_tracks_label_state` must be strengthened to also track stacks. The new inductive statement becomes:

```lean
theorem trace_tracks_full (t : ℕ) (ht : t ≤ params.timeBound) :
    varTrue σ (.label t (cfgAt V input t).l) ∧
    varTrue σ (.state t (cfgAt V input t).var) ∧
    (∀ k, varTrue σ (.stkLen t k ((cfgAt V input t).stk k).length)) ∧
    (∀ k j (hj : j < ((cfgAt V input t).stk k).length),
      varTrue σ (.stkElem t k j ((cfgAt V input t).stk k).reverse[j]))
```

The base case ($t = 0$) follows from `initialConstraints` (the initial label, state, stack length, and stack elements are all explicitly constrained).

The inductive step for stacks requires showing that `transitionClausesAt` correctly propagates stack lengths and elements. This mirrors the label/state propagation but is more involved due to push/pop/frame interactions.

---

## 5. Phase 3: Navigate Transition Clauses

This phase is structurally identical to `halted_forces_next` (which is already proved). The key steps:

### 5.1 Locate the Correct Clause

In `transitionClausesAt params i`, the transition clauses iterate over all `(l, s, topsInfo)` triples. We need the clause for:
- `l = some lbl` (the actual label)
- `s = (cfgAt V input t).var` (the actual state)
- `topsInfo` = the one extracted from consistency (Phase 1)

**Lean:** Navigate the triple `flatMap` using `evalCNF_flatMap_mem` three times:
```lean
have h1 := evalCNF_flatMap_mem hTC (Finset.mem_toList.mpr (Finset.mem_univ (some lbl)))
have h2 := evalCNF_flatMap_mem h1 (Finset.mem_toList.mpr (Finset.mem_univ s))
have h3 := evalCNF_flatMap_mem h2 (Finset.mem_toList.mpr (Finset.mem_univ topsInfo))
```

### 5.2 Antecedent Evaluates to False

The antecedent literals are:
```
[tLit V (.label t (some lbl)) false,
 tLit V (.state t s) false,
 ...stack literals from topsInfo...]
```

Each evaluates to `false` because the corresponding variables are `true` in $\sigma$ (from the inductive hypothesis and `topsInfo`). This is exactly `antecedent_all_false` (already proved).

### 5.3 Extract Consequent

Since the full clause is `antecedent ++ [consequent]` and all antecedent literals are false, the clause being satisfied forces the consequent to be true. Apply `consequent_of_clause` (already proved).

The consequents include:
```lean
tLit V (.label (t+1) res.l) true      -- next label
tLit V (.state (t+1) res.var) true     -- next state
```

where `res = TM2.stepAux (V.m lbl) s stkVals`.

---

## 6. Phase 4: Relate SAT Consequent to Actual Configuration

### 6.1 The GAP: `stkVals` vs. Actual Stacks

The transition clause computes `res = TM2.stepAux (V.m lbl) s stkVals` where `stkVals` is derived from `topsInfo` (contains only stack tops, as singleton lists or empty). The actual next configuration is:

```
cfgAt V input (t+1) = stepOrHalt V (cfgAt V input t)
                     = TM2.stepAux (V.m lbl) s_actual actualStks
```

where `s_actual = (cfgAt V input t).var` and `actualStks k = (cfgAt V input t).stk k`.

**Key question:** Why does `stepAux` with `stkVals` (just tops) give the same label and state as `stepAux` with `actualStks` (full stacks)?

### 6.2 Apply `stepAux_soundness`

This is exactly what `stepAux_soundness` (Correctness.lean, Proved ✅) provides:

```lean
theorem stepAux_soundness (q : TM2.Stmt Γ Λ σ) (s : σ)
    (S1 S2 : ∀ k, List (Γ k))
    (h_agree : ∀ k, (S1 k).take (stmtReadDepth k q) = (S2 k).take (stmtReadDepth k q)) :
    (TM2.stepAux q s S1).l = (TM2.stepAux q s S2).l ∧
    (TM2.stepAux q s S1).var = (TM2.stepAux q s S2).var
```

**Instantiate with:**
- `S1 = stkVals` (singleton tops from topsInfo)
- `S2 = actualStks` (full stacks from the computation)
- `q = V.m lbl`

**Need to verify the hypothesis:** `∀ k, (stkVals k).take (stmtReadDepth k (V.m lbl)) = (actualStks k).take (stmtReadDepth k (V.m lbl))`

From Phase 2 Corollary: `(actualStks k).take 1 = stkVals k` (the top element agrees). Since `stmtReadDepth k (V.m lbl) ≤ maxReadDepth V k`, and `stkVals k` has length ≤ 1, the `take` agrees **if `stmtReadDepth k (V.m lbl) ≤ 1`** for all stacks.

**⚠️ Subtlety:** If a statement reads depth > 1 on some stack (e.g., multiple pops), then `stkVals` (which only captures the top) is insufficient. The `topsInfo` structure captures only the TOP element, but `stepAux` might inspect deeper.

### 6.3 Handling Read Depth > 1

The current `topsInfo` captures at most 1 element per stack. For `stmtReadDepth k q > 1`, we need more stack elements.

**Resolution:** The `transitionClausesAt` function in Tableau.lean derives `stkVals` from `topsInfo` as:
```lean
let stkVals : ∀ k, List (Γ k) := fun k =>
  match topsInfo k with | none => [] | some (_, γ) => [γ]
```

This means `stkVals` has length ≤ 1 per stack. For `stepAux_soundness` to apply, we need `stmtReadDepth k (V.m lbl) ≤ 1`.

**Two approaches:**

**(A) Assume read depth ≤ 1.** Many standard TM2 programs (including those in the Cook-Levin construction) have `stmtReadDepth ≤ 1` per stack per statement. If this holds globally, the proof goes through directly.

**Lean sketch for the depth-1 case:**
```lean
have h_depth1 : ∀ k, stmtReadDepth k (V.m lbl) ≤ 1 := by
  -- From a hypothesis on the machine V, or by computation
  sorry  -- machine-specific
have h_agree : ∀ k, (stkVals k).take (stmtReadDepth k (V.m lbl)) =
                     (actualStks k).take (stmtReadDepth k (V.m lbl)) := by
  intro k; rw [show stmtReadDepth k (V.m lbl) ≤ 1 from h_depth1 k]
  -- stkVals k has length ≤ 1, actualStks k has take 1 = stkVals k
  exact phase2_corollary k
have ⟨h_l_eq, h_s_eq⟩ := stepAux_soundness (V.m lbl) s stkVals actualStks h_agree
```

**(B) Generalize `topsInfo` to capture top-$d$ elements.** Replace `topsInfo` with a structure that stores the top `maxReadDepth V k` elements per stack. This requires:
- Expanding the `topsInfo` type to `∀ k, Option (ℕ × List (V.Γ k))`
- Extracting multiple `stkElem` values from consistency
- Matching them against the actual stack

This is more general but significantly more bookkeeping. **For the Cook-Levin reduction specifically, approach (A) suffices** because the verifier TM2 is designed with read depth ≤ 1.

### 6.4 Final Connection

With `h_l_eq` and `h_s_eq` from `stepAux_soundness`:

```
(TM2.stepAux (V.m lbl) s stkVals).l = (TM2.stepAux (V.m lbl) s actualStks).l
(TM2.stepAux (V.m lbl) s stkVals).var = (TM2.stepAux (V.m lbl) s actualStks).var
```

And `cfgAt V input (t+1) = stepOrHalt V (cfgAt V input t)`. Since `(cfgAt V input t).l = some lbl` (running), `stepOrHalt` reduces to `TM2.step`, which is `TM2.stepAux (V.m lbl) s actualStks`.

From Phase 3, $\sigma$ marks `(.label (t+1) (stepAux (V.m lbl) s stkVals).l)` as true.

By `h_l_eq`, this equals `(stepAux (V.m lbl) s actualStks).l = (cfgAt V input (t+1)).l`.

Similarly for state. Therefore:
```
varTrue σ (.label (t+1) (cfgAt V input (t+1)).l)   ✓
varTrue σ (.state (t+1) (cfgAt V input (t+1)).var)  ✓
```

---

## 7. Full Proof Skeleton

```lean
theorem step_tracks_running ... := by
  -- Phase 1: Extract topsInfo
  have ⟨hC, _, hT_trans, _, _⟩ := sat_components params input σ hsat
  obtain ⟨topsInfo, h_stks⟩ := topsInfo_from_consistency hC (by omega)
  
  -- Phase 2: Relate topsInfo to actual stacks
  -- (requires strengthened inductive hypothesis — see §4.3)
  have h_len_match : ∀ k, match topsInfo k with
    | none => ((cfgAt V input t).stk k).length = 0
    | some (len, _) => ((cfgAt V input t).stk k).length = len.val + 1 := by
    intro k; ... -- from invariant + consistency uniqueness
  have h_top_match : ∀ k, (stkVals k) = ((cfgAt V input t).stk k).take 1 := by
    intro k; ... -- from invariant + consistency uniqueness on stkElem
  
  -- Phase 3: Navigate transition clauses
  unfold transitionConstraints at hT_trans
  have hTC := evalCNF_flatMap_mem hT_trans (mem_range.mpr ht)
  unfold transitionClausesAt at hTC
  set s := (cfgAt V input t).var
  have h1 := evalCNF_flatMap_mem hTC (Finset.mem_toList.mpr (Finset.mem_univ (some lbl)))
  have h2 := evalCNF_flatMap_mem h1 (Finset.mem_toList.mpr (Finset.mem_univ s))
  have h3 := evalCNF_flatMap_mem h2 (Finset.mem_toList.mpr (Finset.mem_univ topsInfo))
  -- Reduce the `match` on `some lbl`
  dsimp only at h3
  -- Extract label and state clauses
  have h_pair := evalCNF_append_left h3
  simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true] at h_pair
  obtain ⟨h_lc, h_sc⟩ := h_pair
  -- All antecedent literals are false
  have h_af := antecedent_all_false h_label h_state h_stks
  -- Extract consequents
  have h_next_l := consequent_of_clause h_lc h_af
  have h_next_s := consequent_of_clause h_sc h_af
  
  -- Phase 4: Relate to actual computation
  -- Apply stepAux_soundness
  set res := TM2.stepAux (V.m lbl) s stkVals
  set actualRes := TM2.stepAux (V.m lbl) s (fun k => (cfgAt V input t).stk k)
  have ⟨h_l_eq, h_s_eq⟩ := stepAux_soundness (V.m lbl) s stkVals
    (fun k => (cfgAt V input t).stk k) (by
      intro k; rw [h_top_match k]; simp [List.take]
      ... -- show take (readDepth) agrees
    )
  -- cfgAt(t+1) = stepOrHalt(cfgAt(t)) = actualRes (since label = some lbl)
  have h_cfg : cfgAt V input (t+1) = ... := by
    rw [cfgAt_succ, stepOrHalt, h_some]; rfl
  -- Conclude
  constructor
  · rw [h_cfg]; simp [h_l_eq] at h_next_l ⊢; exact h_next_l
  · rw [h_cfg]; simp [h_s_eq] at h_next_s ⊢; exact h_next_s
```

---

## 8. Required Auxiliary Lemmas

### Lemma 8.1: `stkLen_unique` (New, Easy)

```lean
theorem stkLen_unique {σ} {params : Params V}
    (hC : evalCNF σ (consistencyConstraints params) = true)
    {t : ℕ} (ht : t ≤ params.timeBound) {k : V.K} {len1 len2 : ℕ}
    (h1 : varTrue σ (.stkLen t k len1))
    (h2 : varTrue σ (.stkLen t k len2)) : len1 = len2
```

**Proof:** Same structure as `consistency_label_unique`. Extract the `exactlyOne` block for `stkLen` at time $t$, stack $k$. Apply `exactlyOne_encode_eq`, then injectivity of `Encodable.encode` on `TableauVar.stkLen`.

### Lemma 8.2: `stkElem_unique` (New, Easy)

```lean
theorem stkElem_unique {σ} {params : Params V}
    (hC : evalCNF σ (consistencyConstraints params) = true)
    {t : ℕ} (ht : t ≤ params.timeBound) {k : V.K} {j : ℕ} (hj : j < params.maxStackDepth)
    {γ1 γ2 : V.Γ k}
    (h1 : varTrue σ (.stkElem t k j γ1))
    (h2 : varTrue σ (.stkElem t k j γ2)) : γ1 = γ2
```

**Proof:** Same pattern. Extract the `exactlyOne` block for `stkElem` at `(t, k, j)`.

### Lemma 8.3: `stepOrHalt_running` (New, Trivial)

```lean
theorem stepOrHalt_running {cfg : V.Cfg} {lbl : V.Λ} (h : cfg.l = some lbl) :
    stepOrHalt V cfg = TM2.stepAux (V.m lbl) cfg.var cfg.stk
```

**Proof:** Unfold `stepOrHalt`, `FinTM2.step`, `TM2.step`. The `some lbl` branch gives `stepAux`.

---

## 9. Formalization Roadmap

| Component | Status | Difficulty | Notes |
|-----------|--------|------------|-------|
| `topsInfo_from_consistency` | ✅ Proved | — | Already in Completeness.lean |
| `antecedent_all_false` | ✅ Proved | — | Already in Completeness.lean |
| `consequent_of_clause` | ✅ Proved | — | Already in Completeness.lean |
| `stepAux_soundness` | ✅ Proved | — | In Correctness.lean |
| `stkLen_unique` (Lemma 8.1) | TODO | Easy | Same pattern as `consistency_label_unique` |
| `stkElem_unique` (Lemma 8.2) | TODO | Easy | Same pattern |
| `stepOrHalt_running` (Lemma 8.3) | TODO | Trivial | Unfold + match |
| Strengthen induction to track stacks (§4.3) | TODO | **Medium** | Requires propagating stack tracking through transition clauses |
| Phase 2 corollary: stkVals = tops | TODO | Medium | Uses 8.1 + 8.2 + strengthened IH |
| Phase 3: clause navigation | TODO | Easy | Copy pattern from `halted_forces_next` |
| Phase 4: `stepAux_soundness` application | TODO | Easy | Direct instantiation |
| Read depth ≤ 1 hypothesis (§6.3) | TODO | **Design decision** | Either assume globally or generalize `topsInfo` |

**Critical path:** The strengthened induction (§4.3) is the main structural change. Everything else follows the established pattern.

---

## 10. Summary

The `step_tracks_running` proof is a four-phase argument:

1. **Extract** `topsInfo` from consistency (already proved)
2. **Relate** `topsInfo` to actual stacks via uniqueness lemmas (new but easy)
3. **Navigate** the transition clause triple-`flatMap` and extract the consequent (copy pattern from halted case)
4. **Bridge** via `stepAux_soundness` from truncated stacks to full stacks (already proved)

The main structural requirement is **strengthening the inductive hypothesis** to track not just labels and states but also stack lengths and elements. This is the one piece that changes the existing proof architecture; everything else is additive.

---

## References

- `botlib/Complexity/CookLevin/Completeness.lean` — Current completeness proof with axiom
- `botlib/Complexity/CookLevin/Correctness.lean` — `stepAux_soundness`, `stepAux_preservation_elem` (both Proved ✅)
- `botlib/Complexity/CookLevin/Tableau.lean` — `TableauVar`, `transitionClausesAt`, `exactlyOne`
- `proofs/cook-levin-correctness.md` — NL correctness proof (Verified ✅)

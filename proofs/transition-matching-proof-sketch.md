# Transition Matching Case — Proof Sketch (Updated 2026-02-12) (by advisor)

This is the proof for the sorry at `Soundness.lean` line 337 (approximately).
The context: after `subst hl; subst hs`, in the `· -- No stkLit evaluates to true` branch.

## Strategy

Replace the sorry with:

```lean
    · -- No stkLit evaluates to true → topsInfo fully matches actual stacks
      -- Extract: every stkLit evaluates to false
      have h_all_false : ∀ lit ∈ stkLits, evalLiteral (traceAssignment c) lit = false := by
        intro lit h_mem
        rcases Bool.eq_false_or_eq_true (evalLiteral (traceAssignment c) lit) with h_t | h_f
        · exfalso; apply h_stk; rw [evalClause, any_eq_true]; exact ⟨lit, h_mem, h_t⟩
        · exact h_f
      -- Per-stack facts from all-false
      have h_stk_none : ∀ k, topsInfo k = none → (c i).stk k = [] := by
        intro k hk
        have h_mem : tLit V (TableauVar.stkLen i k 0) false ∈ stkLits := by
          rw [stkLits_def, mem_flatMap]
          exact ⟨k, Finset.mem_toList.mpr (Finset.mem_univ k), by simp [hk]⟩
        have := h_all_false _ h_mem
        rw [evalTLit_trace] at this; simp [traceValuation] at this; exact this
      have h_stk_some_len : ∀ k len (γ : V.Γ k), topsInfo k = some (len, γ) →
          ((c i).stk k).length = len.val + 1 := by
        intro k len γ hk
        have h_mem : tLit V (TableauVar.stkLen i k (len.val + 1)) false ∈ stkLits := by
          rw [stkLits_def, mem_flatMap]
          exact ⟨k, Finset.mem_toList.mpr (Finset.mem_univ k), by simp [hk]⟩
        have := h_all_false _ h_mem
        rw [evalTLit_trace] at this; simp [traceValuation] at this; exact this
      -- Helper: consequent-true → clause satisfied
      have h_end : ∀ (rest : List Literal) (lit : Literal),
          evalLiteral (traceAssignment c) lit = true →
          evalClause (traceAssignment c) (rest ++ [lit]) = true := by
        intro rest lit h_lit
        simp only [evalClause, any_append, Bool.or_eq_true, any_cons, any_nil, Bool.or_false]
        right; exact h_lit
      have hi' : i < params.timeBound := hi
      cases h_l : (c i).l with
      | none =>
        -- Halted: c(i+1) = c(i), all stacks unchanged
        have h_eq : c (i + 1) = c i := by rw [h_step i hi']; exact step_getD_halted_v2 h_l
        apply evalCNF_append_true
        · simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
          exact ⟨h_end _ _ (by rw [evalTLit_trace]; simp [traceValuation, h_eq, h_l]),
                 h_end _ _ (by rw [evalTLit_trace]; simp [traceValuation, h_eq])⟩
        · apply evalCNF_flatMap_true; intro k _
          cases h_ti : topsInfo k with
          | none =>
            have h_empty := h_stk_none k h_ti
            simp only [evalCNF, all_cons, all_nil, Bool.and_true]
            exact h_end _ _ (by rw [evalTLit_trace]; simp [traceValuation, h_eq, h_empty])
          | some p =>
            obtain ⟨len, γ⟩ := p
            have h_len := h_stk_some_len k len γ h_ti
            simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
            -- stkLen consequent: length at i+1 = len+1 (halted ⟹ c(i+1) = c(i))
            -- stkElem consequent: reverse[len] = γ at i+1 (same as at i)
            exact ⟨h_end _ _ (by rw [evalTLit_trace]; simp [traceValuation, h_eq, h_len]),
                   h_end _ _ (by rw [evalTLit_trace]; simp [traceValuation, h_eq])⟩
            -- NOTE: the stkElem `simp` might fail due to dependent types.
            -- If so, use: `dif_pos (by omega)` then `decide_eq_true_eq`.
            -- The key fact: h_stk_some_elem gives reverse[len] = γ, and h_eq means it's the same at i+1.
      | some lbl =>
        -- Running: use stepAux_soundness for label/state
        have h_actual : c (i + 1) = TM2.stepAux (V.m lbl) (c i).var (c i).stk := by
          rw [h_step i hi']; exact step_getD_running_v2 h_l
        -- stkVals agrees with actual stacks on read depth (BRD)
        set stkVals_fn := (fun k => match topsInfo k with
          | none => ([] : List (V.Γ k)) | some (_, γ) => [γ]) with stkVals_fn_def
        have h_agree : ∀ k, (stkVals_fn k).take (stmtReadDepth k (V.m lbl)) =
            ((c i).stk k).take (stmtReadDepth k (V.m lbl)) := by
          intro k
          have hrd : stmtReadDepth k (V.m lbl) ≤ 1 := by
            have := hBRD lbl k
            rwa [show @stmtReadDepth V.K V.Γ V.Λ V.σ k V.decidableEqK (V.m lbl)
              = stmtReadDepth k (V.m lbl) from by congr 1] at this
          cases h_rd : stmtReadDepth k (V.m lbl) with
          | zero => simp [take]
          | succ n =>
            have hn : n = 0 := by omega
            subst hn; simp only [take]
            cases h_ti : topsInfo k with
            | none =>
              simp [stkVals_fn_def, h_ti]
              have := h_stk_none k h_ti; rw [this]
            | some p =>
              obtain ⟨len, γ⟩ := p
              simp [stkVals_fn_def, h_ti]
              have h_len := h_stk_some_len k len γ h_ti
              -- γ = head of (c i).stk k
              -- reverse (hd :: tl)[tl.length] = hd (via getElem_append_right on reverse_cons)
              rcases h_stk_eq : (c i).stk k with _ | ⟨hd, tl⟩
              · simp [h_stk_eq] at h_len
              · simp only [take, cons.injEq, and_true]
                -- Need: γ = hd
                -- We know: reverse[len] = γ where len = tl.length
                -- reverse (hd :: tl) = reverse tl ++ [hd]
                -- (reverse tl ++ [hd])[tl.length] = hd
                sorry -- See "γ = hd" section below
        have h_sound := stepAux_soundness (V.m lbl) (c i).var stkVals_fn (c i).stk h_agree
        set res := TM2.stepAux (V.m lbl) (c i).var stkVals_fn with res_def
        have h_res_l : res.l = (c (i + 1)).l := by rw [h_actual]; exact h_sound.1
        have h_res_var : res.var = (c (i + 1)).var := by rw [h_actual]; exact h_sound.2
        apply evalCNF_append_true
        · -- Label and state consequents
          simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
          constructor
          · exact h_end _ _ (by rw [evalTLit_trace]; simp [traceValuation]; exact h_res_l.symm)
          · exact h_end _ _ (by rw [evalTLit_trace]; simp [traceValuation]; exact h_res_var.symm)
        · -- Stack consequents for running case
          sorry
```

## Key remaining sorrys

### 1. γ = hd (from reverse[len] = γ)
```lean
-- In context: h_stk_eq : (c i).stk k = hd :: tl, h_len : (hd :: tl).length = len + 1
-- Goal: γ = hd
-- Proof sketch:
-- h_stk_some_elem says: ((c i).stk k).reverse[len]' ... = γ
-- Substituting h_stk_eq: (hd :: tl).reverse[len]' ... = γ
-- (hd :: tl).reverse = tl.reverse ++ [hd]
-- len = tl.length (from h_len: tl.length + 1 = len + 1)
-- (tl.reverse ++ [hd])[tl.length] = hd (getElem_append_right)
-- So γ = hd
```

### 2. Label/state consequents (running case)
The issue: `simp [traceValuation]` may not close the goal because the traceValuation
unfolds to `decide ((c(i+1)).l = res.l)` but `res` is `TM2.stepAux ... stkVals_fn`
while `(c(i+1)).l` is `(TM2.stepAux ... (c i).stk).l`. These are NOT definitionally equal.

Fix: don't use `simp`; instead use `exact h_res_l.symm` after `rw [evalTLit_trace]`.
The traceValuation for label is `decide ((c(i+1)).l = label)`, and the literal says
`tLit V (label (i+1) res.l) true`, which evaluates to `decide ((c(i+1)).l = res.l)`.
Since `h_res_l : res.l = (c(i+1)).l`, we have `(c(i+1)).l = res.l` by symmetry → decide true.

### 3. Stack consequents (running case)
This is the hardest part. For each k:
- stkLen consequent: `newLen = ((c(i+1)).stk k).length`
  where `newLen = oldLen + ns.length - (if isSome then 1 else 0)`
  and `ns = res.stk k = (TM2.stepAux ... stkVals_fn).stk k`
- stkElem consequents: `ns.reverse[j] = ((c(i+1)).stk k).reverse[base + j]`

This requires a `stepAux_stack_agreement` lemma: when stkVals agrees with actual on
read depth, the stack changes (push/pop) produce the same "delta" on both.

## Instance diamond notes
- BRD uses `V.decidableEqK`, section uses `[DecidableEq V.K]`
- Bridge: `rwa [show @stmtReadDepth ... V.decidableEqK ... = stmtReadDepth ... from by congr 1]`
- `step_getD_running_v2`/`step_getD_halted_v2` handle the FinTM2.step diamond

---

## Current Status (2026-02-12, latest)

### What's Proved
- **Halted case**: COMPLETE (all consequents: label, state, stkLen, stkElem)
- **Running case label/state**: COMPLETE (using stepAux_soundness + h_agree)
- **Running case stkLen**: COMPLETE (using stepAux_stk_len_delta from Correctness.lean)

### What Remains: stkElem consequents (1 sorry, line ~534)
For each `(γ, j) ∈ ns.reverse.zipIdx`, need to show:
```
traceValuation c (stkElem (i+1) k₂ (base+j) γ) = true
```
where `base = oldLen - adj`, `ns = (stepAux (V.m lbl) (c i).var stkVals).stk k₂`.

### Approach for stkElem
Need a **stack decomposition theorem** in Correctness.lean:
```lean
theorem stepAux_stk_decomp (q : Stmt) (s : σ) (S_short S_full : ∀ k, List (Γ k))
    (h_agree : ∀ k, (S_short k).take rd = (S_full k).take rd)
    (h_short : ∀ k, S_short k = (S_full k).take rd)
    (k : K) :
    (stepAux q s S_full).stk k = (stepAux q s S_short).stk k ++ (S_full k).drop rd
```
This gives `actual.reverse = ((c i).stk k .drop rd).reverse ++ ns.reverse`,
so `actual.reverse[base+j] = ns.reverse[j] = γ`.

**Alternative**: Per-element version using `stepAux_preservation_elem` for below-rd
and a new `stepAux_stk_top_elem` for at-or-above-rd.

### Key Infrastructure Available
- `stepAux_soundness`: label/state agreement (Correctness.lean)
- `stepAux_preservation_elem`: below-rd elements preserved (Correctness.lean)
- `stepAux_stk_len_delta`: length change is invariant (Correctness.lean, new)

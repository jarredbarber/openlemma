# Blueprint: PolyTimeFst TM

**Status:** Verified ✅
**Reviewed by:** verify
**Goal:** detailed blueprint for constructing a `FinTM2` that computes `Prod.fst` on `pairEncoding` in polynomial time.
**Target:** `botlib/Complexity/Defs.lean` (to witness `PolyTimeFst`).

## 1. Problem Specification

**Input Encoding:** `pairEncoding ea eb`
- $\Gamma_{pair} = \text{Sum } \Gamma_a \Gamma_b$
- Input string on stack $k_0$: `(ea.encode a).map Sum.inl ++ (eb.encode b).map Sum.inr`

**Output Encoding:** `ea`
- $\Gamma_a$
- Output string on stack $k_1$: `ea.encode a`

**Machine Model:** `FinTM2` (Multi-stack Turing Machine).
- $K = \{k_0, k_1, k_{aux}\}$. ($k_{aux}$ for reversal).
- $\Gamma(k_0) = \Gamma_{pair}$.
- $\Gamma(k_1) = \Gamma(k_{aux}) = \Gamma_a$.

## 2. Algorithm: Two-Phase Reversal

A direct transfer from $k_0$ to $k_1$ reverses the order (stack LIFO).
To preserve order, we use two phases:
1.  **Phase 1 (Filter & Reverse):** Pop from $k_0$. If `inl x`, push to $k_{aux}$. If `inr y` or `none`, stop reading and goto Phase 2.
    -   Result on $k_{aux}$: `[an, ..., a1]` (reversed `a`).
2.  **Phase 2 (Reverse Back):** Pop from $k_{aux}$. Push to $k_1$. Repeat until $k_{aux}$ is empty.
    -   Result on $k_1$: `[a1, ..., an]` (correct order).

## 3. Formal Construction

### 3.1 States ($\sigma$)
We need to store the symbol being moved.
-   $\sigma = \text{Option } (\text{Sum } \Gamma_{pair} \Gamma_a)$.
-   Actually, we can just use `Option (Sum \Gamma_a \Gamma_b)` since we only read from $k_0$ (Phase 1) or $k_{aux}$ (Phase 2, type $\Gamma_a$).
-   Let's use a unified type or rely on `FinTM2` flexibility.
-   State: `Option (Sum ea.Γ eb.Γ)` works for Phase 1.
-   State: `Option ea.Γ` works for Phase 2.
-   Unified State: `Sum (Option (Sum ea.Γ eb.Γ)) (Option ea.Γ)`?
-   Simpler: Use `Option (Sum ea.Γ eb.Γ)` throughout. In Phase 2, we just inject `ea.Γ` into `Sum.inl`.

### 3.2 Labels ($\Lambda$)
-   `phase1`: Main loop for filtering and pushing to aux.
-   `phase2`: Main loop for popping aux and pushing to output.

### 3.3 Statements

**Statement `phase1`:**
```lean
TM2.Stmt.pop k₀ (fun _ sym => sym) -- Read input
  (TM2.Stmt.branch (fun sym => match sym with | some (Sum.inl _) => true | _ => false)
    -- Case: inl x (Part of 'a')
    (TM2.Stmt.push k_aux (fun sym => match sym with | some (Sum.inl x) => x | _ => default)
      (TM2.Stmt.goto (fun _ => phase1)))
    -- Case: inr y or none (End of 'a')
    (TM2.Stmt.goto (fun _ => phase2))
  )
```

**Statement `phase2`:**
```lean
TM2.Stmt.pop k_aux (fun _ sym => sym.map Sum.inl) -- Read aux (lift to common state type)
  (TM2.Stmt.branch (fun sym => sym.isSome)
    -- Case: some x
    (TM2.Stmt.push k₁ (fun sym => match sym with | some (Sum.inl x) => x | _ => default)
      (TM2.Stmt.goto (fun _ => phase2)))
    -- Case: none (Aux empty)
    TM2.Stmt.halt
  )
```

## 4. Complexity Analysis

-   **Phase 1:** Reads $|a|$ symbols. Pushes $|a|$ symbols. Stops at first `inr`. Steps $\approx |a|$.
-   **Phase 2:** Pops $|a|$ symbols. Pushes $|a|$ symbols. Steps $\approx |a|$.
-   **Total Time:** $O(|a|) = O(n)$. Polynomial.
-   **Space:** Aux stack uses $O(|a|)$. Output uses $O(|a|)$.

## 5. Lean Structure

```lean
def polyTimeFstTM {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) : FinTM2 :=
  { K := Fin 3 -- 0=input, 1=output, 2=aux
    Γ := fun k => match k with
      | 0 => (pairEncoding ea eb).Γ
      | _ => ea.Γ
    Λ := Bool -- false=phase1, true=phase2
    σ := Option (Sum ea.Γ eb.Γ)
    ...
    m := fun l => match l with
      | false => -- Phase 1 stmt
      | true  => -- Phase 2 stmt
  }
```

This blueprint provides the exact logic `formalize` needs to implement the witness for `PolyTimeFst`.

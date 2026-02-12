# Blueprint: PolyTimeFst TM

**Status:** Draft ✏️
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
- $K = \{k_0, k_1\}$.
- $\Gamma(k_0) = \Gamma_{pair}$.
- $\Gamma(k_1) = \Gamma_a$.

## 2. Algorithm

The algorithm is a simple linear scan and filter.

1.  **State `start`**:
    -   Peek/Pop from input stack $k_0$.
    -   **Case `some (inl x)`**:
        -   The symbol belongs to the first component $a$.
        -   Push `x` onto the output stack $k_1$.
        -   Loop back to `start`.
    -   **Case `some (inr y)`**:
        -   The symbol belongs to the second component $b$.
        -   We have finished reading $a$.
        -   Transition to `halt` (we don't need to consume $b$, just stop).
    -   **Case `none`** (Empty):
        -   End of input.
        -   Transition to `halt`.

## 3. Formal Construction

### 3.1 States ($\sigma$)
We only need one active state.
-   $\sigma = \text{Unit}$ (or `Bool` if we want distinct start/halt, but `FinTM2` handles halting via `Option Label`).
-   Let's use `Unit`. `initialState = ()`.

### 3.2 Labels ($\Lambda$)
We need labels for the transitions.
-   `read`: The main loop state.
-   `write(x)`: A parameterized label to handle pushing the read symbol?
    -   Actually, `TM2.Stmt` can combine pop and push.
    -   We can define the `Stmt` for `read` to do the logic.

### 3.3 Statement (`read`)
The statement at label `main` corresponds to the algorithm:

```lean
TM2.Stmt.pop k₀ (fun _ s => -- read symbol `s` from input
  match s with
  | some (Sum.inl x) => 
      -- Found part of 'a', keep it.
      (s, some x) -- Store 'x' in auxiliary state/output? 
      -- Wait, pop takes a function `σ → Option Γ → σ`. 
      -- It updates the internal state.
      -- We need to push to k₁.
      -- We can't push immediately in the `pop` function.
      -- We need to branch or use the value.
  | _ => ...
)
```

**Revised Stmt using `peek` + `pop` + `push`:**

It's cleaner to `pop` the input into the internal state `σ`, then `branch` on the value.
Let `σ = Option \Gamma_a`. Initial state `none`.

**Statement `loop`:**
1.  **Pop $k_0$**: Update state `s` with the popped symbol.
    -   If `inl x`, set state to `some x`.
    -   If `inr y` or `none`, set state to `none` (flag to halt).
2.  **Branch**: Check state.
    -   If `some x`:
        -   **Push $k_1$**: Push `x`.
        -   **Goto `loop`**.
    -   If `none`:
        -   **Halt**.

### 3.4 Refined State Space
To implement the above:
-   $\sigma = \text{Option } \Gamma_a$.
-   `initialState` doesn't matter for the first step, but let's say `none`.
-   Wait, we need to handle the first read correctly.

**Better State:**
Use `σ = Option (Sum \Gamma_a \Gamma_b)`.
But we only need to write `\Gamma_a`.

**Optimized Stmt (Stateless approach using `load`?):**
`FinTM2` statements are flexible.
We can define the statement for `main` as:

```lean
TM2.Stmt.pop k₀ (fun _ sym => sym) -- Store popped symbol in state
  (TM2.Stmt.branch (fun sym => 
      match sym with 
      | some (Sum.inl _) => true 
      | _ => false)
    -- Case: inl x
    (TM2.Stmt.push k₁ (fun sym => 
        match sym with 
        | some (Sum.inl x) => x 
        | _ => default) -- proven unreachable by branch
      (TM2.Stmt.goto (fun _ => main)))
    -- Case: inr y or none
    TM2.Stmt.halt
  )
```

## 4. Complexity Analysis

-   **Time:** The machine performs 1 iteration per symbol of `encode(a)`.
    -   It stops as soon as it hits the first `inr`.
    -   Total steps = $|encode(a)| + 1$.
    -   This is linear in input size $n$.
    -   $T(n) = O(n)$.
-   **Space:** It writes exactly `encode(a)` to the output stack. $O(n)$.

## 5. Lean Structure

```lean
def polyTimeFstTM {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) : FinTM2 :=
  { K := Bool -- k₀=false, k₁=true
    Γ := fun k => if k then ea.Γ else (pairEncoding ea eb).Γ
    Λ := Unit -- just one label
    σ := Option (Sum ea.Γ eb.Γ) -- hold the read symbol
    ...
    m := fun () => 
      TM2.Stmt.pop false (fun _ s => s) $
        TM2.Stmt.branch (fun s => match s with | some (Sum.inl _) => true | _ => false)
          (TM2.Stmt.push true (fun s => match s with | some (Sum.inl x) => x | _ => default)
            (TM2.Stmt.goto (fun _ => ())))
          TM2.Stmt.halt
  }
```

This blueprint provides the exact logic `formalize` needs to implement the witness for `PolyTimeFst`.

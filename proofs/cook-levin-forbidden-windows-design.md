# Design Note: Forbidden Windows for Cook-Levin with TM2

**Status:** Strategic guidance for Phase 3 formalization  
**Author:** advisor  
**Date:** 2026-02-12

## The Challenge

Standard Cook-Levin uses single-tape TMs with a simple `(state, symbol) → (state, symbol, direction)` transition function. The "window" is a 2×3 grid of tape cells, and forbidden windows are enumerable because the alphabet and state set are finite.

Our formalization uses Mathlib's `TM2` model, which has:
- Multiple stacks (indexed by `K : Type`, `Fintype K`)
- Each stack has its own alphabet (`Γ : K → Type`)
- A step is computed by `stepAux`, which recursively processes a `Stmt` tree (push/pop/peek/branch/load/goto/halt)
- One logical "step" (`step V.m`) can push/pop multiple stacks

This means the "local window" approach doesn't directly apply — stacks have variable length and a single step can affect all of them.

## Design: Abstract State Transition Approach

Instead of encoding individual stack cells as in single-tape Cook-Levin, we observe:

### Key Observation
`step V.m` is a total function from `Cfg` to `Option Cfg`. A `Cfg` consists of:
- `l : Option V.Λ` (label, finitely many values)
- `var : V.σ` (state, finitely many values)  
- `stk : ∀ k, List (V.Γ k)` (stacks, **unbounded**)

The stacks are unbounded, so we can't enumerate all `Cfg` values. But we CAN observe that `step` only reads the **top** of each stack and modifies the **top** of each stack.

### What step reads and writes
Looking at `stepAux`:
- `push k f q`: pushes `f v` onto stack `k` (reads `v`, writes top of `k`)
- `pop k f q`: reads `(S k).head?`, updates `v`, pops top of `k`
- `peek k f q`: reads `(S k).head?`, updates `v`, doesn't modify stacks
- `load a q`: updates `v := a v`, no stack access
- `branch f q₁ q₂`: reads `v`, branches
- `goto f`: sets new label
- `halt`: halts

So **within one step**, the machine:
1. Reads the current label and state
2. Reads `head?` of various stacks (determined by the `Stmt` tree)
3. Pushes/pops the tops of various stacks
4. Sets a new label and state

### Encoding Variables (for TM2)

For a computation of length `T = p(n)`:

```
TableauVariable V :=
  | label (i : Fin (T+1)) (l : Option V.Λ)   -- label at time i
  | state (i : Fin (T+1)) (s : V.σ)           -- state at time i
  | stkElem (i : Fin (T+1)) (k : V.K) (j : Fin (T+1)) (γ : V.Γ k)
                                                -- stack k, position j, time i has symbol γ
  | stkLen (i : Fin (T+1)) (k : V.K) (len : Fin (T+2))
                                                -- stack k at time i has length len
```

### Constraint Groups

**Group 1: Consistency** (same as current `CookLevin.lean`)
- Exactly one label per timestep
- Exactly one state per timestep
- Exactly one symbol per stack position per timestep
- Exactly one length per stack per timestep

**Group 2: Initial configuration**
- Label at time 0 = `some V.main`
- State at time 0 = `V.initialState`
- Input stack loaded with encoded input
- Other stacks empty

**Group 3: Stack frame preservation**
- If `stkLen(i, k) = len` and position `j < len - 1`, then `stkElem(i, k, j) = stkElem(i+1, k, j)`  
  (Only the top element can change)

**Group 4: Transition consistency**
This is the key group. For each timestep `i`:

The transition is determined by:
- `label(i) = l`
- `state(i) = s`  
- For each stack `k`: `stkTop(i, k) = head? of stack k` (derivable from `stkLen` and `stkElem`)

Given these inputs, `stepAux (V.m l) s stacks` deterministically produces:
- `label(i+1) = l'`
- `state(i+1) = s'`
- For each stack `k`: new top / length change

Since `l`, `s`, and the stack tops are all from finite types, we CAN enumerate all possible input tuples:
```
(l : Option V.Λ) × (s : V.σ) × (∀ k, Option (V.Γ k))
```

For each such tuple, compute what the next configuration's (label, state, stack tops, stack lengths) should be. Emit clauses enforcing:
```
label(i) = l ∧ state(i) = s ∧ ∀ k, top(i,k) = γ_k  
  →  label(i+1) = l' ∧ state(i+1) = s' ∧ ∀ k, stackChange(i,k) consistent
```

As CNF (implication = ¬antecedent ∨ consequent):
```
¬label(i,l) ∨ ¬state(i,s) ∨ ¬top(i,k₁,γ₁) ∨ ... ∨ label(i+1,l')
¬label(i,l) ∨ ¬state(i,s) ∨ ¬top(i,k₁,γ₁) ∨ ... ∨ state(i+1,s')
...
```

### Implementation in Lean

```lean
/-- The "abstract top" of stacks — what step reads. -/
structure StepInput (V : FinTM2) where
  label : Option V.Λ
  state : V.σ
  tops : ∀ k, Option (V.Γ k)

/-- Compute the step output given abstract inputs. -/
def abstractStep (V : FinTM2) (inp : StepInput V) : Option (StepOutput V) :=
  -- Build a minimal Cfg with stacks containing just the tops
  -- Run step V.m on it
  -- Extract the output
  sorry -- But this needs care: stepAux may read deeper into stacks!
```

## CRITICAL ISSUE: stepAux reads beyond the top

**This is the main complication.** Consider a `Stmt` like:
```
pop k₁ f₁ (pop k₁ f₂ (goto g))
```
This pops `k₁` twice — reading both the top and second element. The "abstract top" isn't sufficient!

### Resolution Options

**Option A: Bound the read depth.** For a given `Stmt` tree, compute the maximum number of pops on each stack. This gives a finite "read window" depth per stack. The window variables then include the top `d` elements of each stack (where `d` is the max read depth for that stack in the whole program).

**Option B: Flatten to single-operation steps.** Decompose each `Stmt` into individual push/pop/peek operations, each a separate "micro-step." Then each micro-step truly reads only the top. The tableau has more timesteps but simpler transitions.

**Option C: Work at the Cfg level directly.** Don't try to decompose into local windows. Instead, define the transition constraint as: "the entire Cfg at time `i+1` equals `step V.m` applied to the Cfg at time `i`." Enumerate all possible (finite) combinations of (label, state, top-d-elements-of-each-stack) and hardcode the transition.

### Recommendation: Option A (Bounded Read Depth)

For any `FinTM2` machine, the statement tree for each label is finite and fixed. We can compute `maxDepth : V.K → ℕ` — the maximum number of pops on stack `k` within any single step. Then:

```lean
def maxReadDepth (V : FinTM2) (k : V.K) : ℕ :=
  Finset.sup Finset.univ (fun l => stmtReadDepth (V.m l) k)
```

The "window" at timestep `i` includes:
- Label, state
- Top `maxReadDepth V k` elements of each stack `k`

This is a finite set, so we can enumerate all valid transitions. The number of clauses per timestep is bounded by the product of all the type cardinalities, which is a constant (depending on the machine, not the input).

## Summary

| Approach | Complexity | Implementation Effort | Proof Difficulty |
|----------|------------|----------------------|------------------|
| Option A (bounded depth) | Best | Medium | Medium |
| Option B (micro-steps) | More timesteps | Easy | Hard (need to show equivalence) |
| Option C (full Cfg) | Same | Easy | Hard (stacks are infinite objects) |

**Recommendation:** Option A, but if the verifier machine we construct for Cook-Levin is simple enough (e.g., each step does at most one pop per stack), then the max read depth is 1 and the "abstract top" approach works directly.

**Next action:** When formalize starts on `CookLevin/Tableau.lean`, examine the actual verifier machine to determine `maxReadDepth`. If it's 1 for all stacks, the encoding is straightforward.

# Blueprint: Cook-Levin CNF Formalization

**Status:** Draft ✏️
**Goal:** Provide a concrete technical specification for the variables and clauses of the Cook-Levin reduction ($\phi_w$) to guide the Lean formalization.
**References:** `proofs/cook-levin-tableau.md`, `proofs/cook-levin-correctness.md`

## 1. Constants and Dimensions

Let $M$ be the TM2 verifier (deterministic, multi-stack).
For simplicity in this blueprint, we assume the **single-tape abstraction** used in the NL proofs, but we provide indexing that generalizes to multi-stack.

*   $n = |w|$: Input size.
*   $T = p(n)$: Time bound.
*   $m = |\Gamma|$: Tape alphabet size. Symbols indexed $0 \dots m-1$.
*   $q = |Q|$: State set size. States indexed $0 \dots q-1$.

## 2. Variable Indexing

We map high-level variables to a single `Nat` index space.
The total number of variables is roughly $N_{var} \approx T^2 (m + 1 + q)$.

We partition the `Nat` space into three ranges:
1.  **Cell Variables (`C`):** $C_{i,j,s}$ - Cell $j$ at time $i$ contains symbol $s$.
2.  **Head Variables (`H`):** $H_{i,j}$ - Head is at position $j$ at time $i$.
3.  **State Variables (`S`):** $S_{i,k}$ - Machine is in state $k$ at time $i$.

**Indexing Formula:**
Let `idx(i, j, k, type)` be the mapping.
A simpler flat scheme:
*   `offset_C = 0`
*   `size_C = (T+1) * (T+1) * m`
*   `idx_C(i, j, s) = offset_C + i * ((T+1)*m) + j * m + s`

*   `offset_H = size_C`
*   `size_H = (T+1) * (T+1)`
*   `idx_H(i, j) = offset_H + i * (T+1) + j`

*   `offset_S = offset_H + size_H`
*   `size_S = (T+1) * q`
*   `idx_S(i, k) = offset_S + i * q + k`

This mapping is bijective for valid ranges and computable in polynomial time.

## 3. Clause Specifications

We define the clauses as lists of literals (`Literal.pos` or `Literal.neg`).

### 3.1 Cell Consistency ($\phi_{\text{cell}}$)
For each $(i, j) \in \{0\dots T\}^2$:
1.  **At least one symbol:**
    `[pos C(i,j,0), pos C(i,j,1), ..., pos C(i,j,m-1)]`
2.  **At most one symbol:**
    For every pair distinct $s, s' \in \Gamma$:
    `[neg C(i,j,s), neg C(i,j,s')]`

**Head Uniqueness:**
For each $i \in \{0\dots T\}$:
1.  **At least one head:**
    `[pos H(i,0), ..., pos H(i,T)]`
2.  **At most one head:**
    For distinct $j, j'$: `[neg H(i,j), neg H(i,j')]`

**State Uniqueness:**
For each $i \in \{0\dots T\}$:
1.  **At least one state:** `[pos S(i,0), ..., pos S(i,q-1)]`
2.  **At most one state:** Distinct $k, k'$: `[neg S(i,k), neg S(i,k')]`

### 3.2 Start Configuration ($\phi_{\text{start}}$)
Unit clauses enforcing the initial state at $t=0$.
1.  **State:** `[pos S(0, q_start)]` (and `neg` for all other states? Implied by uniqueness).
2.  **Head:** `[pos H(0, 0)]` (and `neg` for others? Implied).
3.  **Tape:**
    *   For $0 \le j < n$: `[pos C(0, j, w[j])]`.
    *   For $n \le j \le T$: `[pos C(0, j, blank)]`.

### 3.3 Acceptance ($\phi_{\text{accept}}$)
The machine accepts if it enters $q_{accept}$ at any time step.
`[pos S(0, q_accept), pos S(1, q_accept), ..., pos S(T, q_accept)]`

*Note for 3-SAT:* This clause is long. The Tseitin transformation will break it down. For now, a single wide clause is valid.

### 3.4 Transitions ($\phi_{\text{move}}$)
This ensures consistency between row $i$ and row $i+1$.
We apply constraints for every window centered at $j$.

**Variables involved in window $(i, j)$:**
*   **Time $i$:** $H(i, j-1), H(i, j), H(i, j+1)$ (Head presence)
*   **Time $i$:** $C(i, j-1, \cdot), C(i, j, \cdot), C(i, j+1, \cdot)$ (Content)
*   **Time $i$:** $S(i, \cdot)$ (State)
*   **Time $i+1$:** $C(i+1, j, \cdot)$ (New content)
*   **Time $i+1$:** $H(i+1, j)$ (New head presence) -- *Wait, head position is usually global, but local effect is checkable?*
    *   Correct logic: The value of $C(i+1, j)$ is determined by the window. The presence of head at $H(i+1, j)$ is also determined by the window (did it move here?).

**Logic as CNF:**
Instead of manually deriving CNF for every possible transition rule, we use a generic "legal window" predicate.
Let a window configuration be a tuple $W = (s_{j-1}, s_j, s_{j+1}, q, h_{pos})$.
$h_{pos} \in \{L, C, R, None\}$ denotes where the head is relative to $j$.
Let $\text{Legal}(W, s'_j)$ be true if the transition function $\delta$ permits cell $j$ to become $s'_j$ given window $W$.

The constraint is: "If the configuration at $i$ matches $W$, then $C(i+1, j)$ must be consistent with $\text{Legal}(W)$."
In CNF, we write implications:
`WindowIs(W) => (ConsistentOutcome)`
$\neg \text{WindowIs}(W) \lor \text{Outcome}_1 \lor \dots$

**Simplified Transition encoding (Standard):**
Enumerate all *valid* $2 \times 3$ windows.
A $2 \times 3$ window is valid if the bottom center cell and head/state are consistent with the top row.
Let $V$ be the set of valid windows.
For each cell $(i, j)$, assert:
$$ \bigvee_{v \in V} (\text{Window at } (i, j) \text{ matches } v) $$
Since "Window matches v" is a conjunction of literals, this becomes a DNF.
We convert DNF to CNF by distribution or using auxiliary variables?
**Standard Cook-Levin Trick:**
Since the window size is constant ($6$ cells + state), the number of variables is constant.
We can simply list the *forbidden* windows.
For each invalid assignment to the window variables, add a clause forbidding it.
Clause: `[neg var1, neg var2, ...]` where `var` are the literals of the bad assignment.

**Variables in window $(i,j)$:**
*   $C_{i, j-1}, C_{i, j}, C_{i, j+1}$
*   $C_{i+1, j}$
*   $H_{i, j-1}, H_{i, j}, H_{i, j+1}$
*   $H_{i+1, j}$
*   $S_{i}, S_{i+1}$

Iterate over all truth assignments to these variables. If an assignment represents an invalid transition according to $\delta$, generate a clause forbidding it.

## 4. Multi-Stack Adaptation (TM2)

For the actual formalization, $M$ is a TM2 with $k$ stacks.
*   **Cell Variables:** $C_{i,j,s,k}$ - Stack $k$, cell $j$, time $i$, symbol $s$.
*   **Head Variables:** $H_{i,j,k}$ - Stack $k$ head is at $j$ at time $i$.
*   **State:** $S_{i,q}$ - Same.

The transition logic checks all $k$ stacks simultaneously.
A "window" is now a collection of $k$ windows (one per stack).
The "forbidden assignment" approach still works: the number of variables in the locality is still constant (though larger: $k \times \text{window\_size}$). Since $k$ is fixed for the machine, this is polynomial (constant factor).

## 5. Formalization Plan

1.  Define `CookLevin.Variables` inductive type (or the mapping to Nat).
2.  Define `CookLevin.genClauses(M, w, T)` function.
3.  Prove `evalCNF` on `genClauses` with a "good" assignment returns true.
4.  Prove any satisfying assignment yields a valid trace.

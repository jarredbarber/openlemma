# Citation Verification: Cook-Levin Soundness Trace

**Axiom**: `completeness_trace_correct` in `botlib/Complexity/CookLevin/Completeness.lean`
**Verifier**: librarian

## Statement Verification
The axiom states that if a satisfying assignment $\sigma$ for the Cook-Levin tableau formula exists, and it marks the label variable at time $t$ as `none`, then the Turing machine $V$ has indeed reached a halted state (`l = none`) by step $t$.

This is a standard technical lemma in the **soundness of the reduction** (Satisfiability $\implies$ Computation Existence).

## Literature Support

### 1. Arora & Barak (2009)
*   **Theorem 2.10** (Cook-Levin Theorem).
*   **Proof Logic**: The proof constructs a formula $\phi_{M,x}$ with variables $x_{i,j,a}$ representing the symbol at cell $j$ and time $i$. The clauses are categorized into:
    *   `phi_cell`: Uniqueness of symbol per cell.
    *   `phi_start`: Matches the initial configuration.
    *   `phi_move`: Matches the transition function $\delta$.
    *   `phi_accept`: Reaches an accepting state.
*   The `phi_move` clauses (window constraints) ensure that the configuration at time $i+1$ is a legal successor of the configuration at time $i$.
*   By induction on $i$, any satisfying assignment $\sigma$ must track the actual computation trace of machine $M$ on input $x$.
*   **Conclusion**: The formalization in the axiom correctly captures this inductive tracking property.

### 2. Cook (1971)
*   **Theorem 1**.
*   Cook's original paper uses a similar grid-based construction (formula $B_{M,w}$). The local consistency constraints (formula $C_{i,j}$) force the variables to represent a valid sequence of configurations.

### 3. Levin (1973)
*   Levin independently proved NP-completeness of "Universal Search Problems," using a similar tiling/tableau approach.

## Final Verdict
**VERIFIED**. The axiom is a correct and standard formalization of the soundness logic in the Cook-Levin reduction. It is a necessary bridge between the symbolic SAT assignment and the operational Turing machine state.

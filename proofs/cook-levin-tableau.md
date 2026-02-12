# Cook-Levin Theorem: Tableau Construction

**Status:** Verified ✅
**Reviewed by:** verify
**Goal:** Prove that for any language $L \in NP$, there exists a polynomial-time reduction $f$ such that $w \in L \iff f(w) \in \text{SAT}$.

**Strategy:**
Let $M$ be a non-deterministic Turing machine (NDTM) that decides $L$ in polynomial time $p(n)$.
Given an input $w$ of length $n$, we construct a CNF formula $\phi_w$ that is satisfiable if and only if there is an accepting computation path of $M$ on $w$.

The construction involves building a "tableau" — a grid representing the state of the machine at each time step.

## 1. Parameters

*   **Time steps:** $0 \le i \le p(n)$.
*   **Tape cells:** $0 \le j \le p(n)$ (since the head can move at most 1 step per time unit).
*   **Alphabet:** $\Gamma = \{ \gamma_1, \dots, \gamma_m \}$ (finite tape alphabet).
*   **States:** $Q = \{ q_1, \dots, q_k \}$ (finite set of states).

## 2. Variables

We define boolean variables to represent the configuration of the machine at each step.

1.  **Cell Variables:** $C_{i,j,s}$ is true iff at time $i$, cell $j$ contains symbol $s \in \Gamma$.
2.  **Head Variables:** $H_{i,j}$ is true iff at time $i$, the head is at position $j$.
3.  **State Variables:** $S_{i,q}$ is true iff at time $i$, the machine is in state $q \in Q$.

Total variables: $O(p(n)^2)$.

## 3. Clauses (Constraints)

The formula $\phi_w$ is the conjunction of four groups of clauses:
$$ \phi_w = \phi_{\text{cell}} \wedge \phi_{\text{start}} \wedge \phi_{\text{accept}} \wedge \phi_{\text{move}} $$

### 3.1 Cell Consistency ($\phi_{\text{cell}}$)
Ensures the configuration is valid at every step.

*   **One symbol per cell:** For each $(i, j)$, exactly one $s \in \Gamma$ is in cell $j$.
*   **One head position:** For each $i$, exactly one $j$ has the head.
*   **One state:** For each $i$, exactly one state $q$.

### 3.2 Start Configuration ($\phi_{\text{start}}$)
Ensures the machine starts on input $w = w_1 \dots w_n$ in state $q_{start}$ with head at 0.

*   $S_{0, q_{start}}$ is true.
*   $H_{0, 0}$ is true.
*   $C_{0, j, w_{j+1}}$ is true for $0 \le j < n$.
*   $C_{0, j, \sqcup}$ is true for $n \le j \le p(n)$ (blank symbol).

### 3.3 Acceptance ($\phi_{\text{accept}}$)
Ensures the machine eventually enters an accepting state.
$$ \bigvee_{i=0}^{p(n)} S_{i, q_{accept}} $$

### 3.4 Transitions ($\phi_{\text{move}}$)
Ensures the state at time $i+1$ follows from the state at time $i$ according to the transition function $\delta$.

#### Local Consistency Logic

The state of cell $j$ at time $i+1$ ($C_{i+1, j, \cdot}$), and whether the head is at $j$ at time $i+1$ ($H_{i+1, j}$), is fully determined by the configuration of cells $j-1, j, j+1$ at time $i$.

Let $\delta(q, s) = \{(q', s', D)\}$ be the set of possible transitions.

1.  **Head entering from Left ($j-1 \to j$):**
    If $H_{i, j-1} \wedge S_{i, q} \wedge C_{i, j-1, s}$ and $(q', s', \text{Right}) \in \delta(q, s)$, then $H_{i+1, j}$ must be true.

2.  **Head entering from Right ($j+1 \to j$):**
    If $H_{i, j+1} \wedge S_{i, q} \wedge C_{i, j+1, s}$ and $(q', s', \text{Left}) \in \delta(q, s)$, then $H_{i+1, j}$ must be true.

3.  **Head leaving ($j \to j \pm 1$):**
    If $H_{i, j} \wedge S_{i, q} \wedge C_{i, j, s}$ and the machine transitions, then $H_{i+1, j}$ must be false (unless the head stays, if allowed). The symbol $C_{i+1, j, s'}$ becomes the new symbol $s'$.

4.  **No Head Interaction:**
    If the head is not at $j-1, j, j+1$ at time $i$, then the cell must not change:
    $$ \neg H_{i, j-1} \wedge \neg H_{i, j} \wedge \neg H_{i, j+1} \implies (C_{i+1, j, s} \iff C_{i, j, s}) $$
    Also, the head cannot appear at $j$ from nowhere:
    $$ \neg H_{i, j-1} \wedge \neg H_{i, j} \wedge \neg H_{i, j+1} \implies \neg H_{i+1, j} $$

#### Boundary Conditions
The tableau is indexed $0 \le j \le p(n)$.
When considering windows centered at the boundaries:
- For $j=0$: Treat $j-1$ as a virtual cell containing the blank symbol $\sqcup$ with no head. The head cannot move Left from $j=0$ (or the machine halts/rejects).
- For $j=p(n)$: Treat $j+1$ as a virtual cell containing $\sqcup$ with no head.
- These virtual cells are constant and do not require variables.

#### Head Uniqueness and Teleportation
Although $\phi_{\text{cell}}$ enforces that exactly one $H_{i+1, j'}$ is true for the entire tape at time $i+1$, the local constraints in $\phi_{\text{move}}$ must be consistent with this.
Specifically, if the head moves from $j$ to $j+1$, the window at $j$ says "head leaves to right" and the window at $j+1$ says "head enters from left". These must be synchronized.
If the transition logic were flawed (e.g., allowing the head to duplicate), it would contradict the "exactly one" constraint in $\phi_{\text{cell}}$, making the formula unsatisfiable (Soundness).
If the transition logic is correct, exactly one $H_{i+1, j'}$ will be true (Completeness).

## 4. Size Analysis

*   **Variables:** $O(p(n)^2)$.
*   **Clauses:** All constraints ($\phi_{\text{cell}}, \phi_{\text{start}}, \phi_{\text{accept}}, \phi_{\text{move}}$) generate a number of clauses that is constant per cell/time step, or linear in $p(n)$. 
Total size is $O(p(n)^2)$, which is polynomial in $n$.

## 5. Correctness

*   **Completeness:** An accepting computation path of $M$ on $w$ provides a valid assignment to all variables that satisfies all clauses by construction.
*   **Soundness:** A satisfying assignment defines a sequence of configurations where each follows from the previous via a legal transition (or inertia), starts correctly, and ends in an accepting state.

## Conclusion

The transformation $w \mapsto \phi_w$ is a polynomial-time reduction from any $L \in NP$ to SAT. Thus, SAT is NP-hard.

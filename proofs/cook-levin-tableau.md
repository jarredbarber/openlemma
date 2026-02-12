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

#### Local Consistency (Windows)
For each cell $j$ and time $i$, the content $C_{i+1, j, s}$, $H_{i+1, j}$, and $S_{i+1, q}$ are determined by the $2 \times 3$ window centered at $(i, j)$.

#### Boundary Conditions
For $j=0$ and $j=p(n)$, we assume virtual cells $j=-1$ and $j=p(n)+1$ that always contain the blank symbol $\sqcup$ and never contain the head. This allows $2 \times 3$ windows to be applied uniformly.

#### Head Movement and State Change
If $H_{i,j}$ and $S_{i,q}$ and $C_{i,j,s}$ are true, then the state $S_{i+1, q'}$, head position $H_{i+1, j \pm 1}$, and new symbol $C_{i+1, j, s'}$ must satisfy $(q', s', \text{Dir}) \in \delta(q, s)$. 
Since $\delta$ is non-deterministic, the constraint is a disjunction over all legal transitions in $\delta$.

#### Inertia (No-Change Rule)
If the head is not at $j$ at time $i$, and does not move to $j$ at time $i+1$, the symbol in cell $j$ remains unchanged:
$$ (\neg H_{i, j} \wedge \neg H_{i+1, j}) \implies (C_{i, j, s} \iff C_{i+1, j, s}) $$

## 4. Size Analysis

*   **Variables:** $O(p(n)^2)$.
*   **Clauses:** All constraints ($\phi_{\text{cell}}, \phi_{\text{start}}, \phi_{\text{accept}}, \phi_{\text{move}}$) generate a number of clauses that is constant per cell/time step, or linear in $p(n)$. 
Total size is $O(p(n)^2)$, which is polynomial in $n$.

## 5. Correctness

*   **Completeness:** An accepting computation path of $M$ on $w$ provides a valid assignment to all variables that satisfies all clauses by construction.
*   **Soundness:** A satisfying assignment defines a sequence of configurations where each follows from the previous via a legal transition (or inertia), starts correctly, and ends in an accepting state.

## Conclusion

The transformation $w \mapsto \phi_w$ is a polynomial-time reduction from any $L \in NP$ to SAT. Thus, SAT is NP-hard.

# Cook-Levin Theorem: Tableau Construction

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
    $$ \bigvee_{s \in \Gamma} C_{i,j,s} \wedge \bigwedge_{s \neq s'} (\neg C_{i,j,s} \vee \neg C_{i,j,s'}) $$
*   **One head position:** For each $i$, exactly one $j$ has the head.
    $$ \bigvee_{j} H_{i,j} \wedge \bigwedge_{j \neq j'} (\neg H_{i,j} \vee \neg H_{i,j'}) $$
*   **One state:** For each $i$, exactly one state $q$.
    $$ \bigvee_{q \in Q} S_{i,q} \wedge \bigwedge_{q \neq q'} (\neg S_{i,q} \vee \neg S_{i,q'}) $$

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

For each cell $j$ and time $i$, the content $C_{i+1, j, s}$ depends only on the neighborhood at time $i$: cells $j-1, j, j+1$.
We define valid "windows" of size $2 \times 3$ that represent legal local transitions.

Let a window be a tuple $(s_{j-1}, s_j, s_{j+1}, q, h_{pos})$ at time $i$.
A window is **legal** if it is consistent with $\delta$.

For every cell $j$ and time $i$, we enforce that the $2 \times 3$ window centered at $(i, j)$ is legal.
This can be written as a large set of implications or CNF clauses connecting variables at time $i$ and $i+1$.

Specifically, if the head is not at $j$ (and not entering $j$), the symbol must remain unchanged:
$$ (\neg H_{i, j} \wedge \neg H_{i+1, j}) \implies (C_{i, j, s} \iff C_{i+1, j, s}) $$

If the head is at $j$, the change must match a transition in $\delta$.

## 4. Size Analysis

*   **Variables:** $O(p(n)^2)$.
*   **Clauses:**
    *   $\phi_{\text{cell}}$: $O(p(n)^2)$ (constant number per cell).
    *   $\phi_{\text{start}}$: $O(p(n))$.
    *   $\phi_{\text{accept}}$: $O(p(n))$.
    *   $\phi_{\text{move}}$: $O(p(n)^2)$ (constant number per cell/time pair).

Total size is $O(p(n)^2)$, which is polynomial in $n$.

## 5. Correctness

*   **Completeness:** If $M$ accepts $w$, there is a sequence of configurations. Setting the variables according to this sequence satisfies all clauses.
*   **Soundness:** If $\phi_w$ is satisfiable, the variables describe a valid sequence of configurations starting from $w$ and ending in an accepting state. Thus $M$ accepts $w$.

## Conclusion

The transformation $w \mapsto \phi_w$ is a polynomial-time reduction from $L$ to SAT.
Since $L$ was an arbitrary language in NP, SAT is NP-hard.
Combined with SAT $\in$ NP, SAT is NP-complete.

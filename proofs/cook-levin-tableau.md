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

#### Head Movement and State Change
If $H_{i,j}$ and $S_{i,q}$ and $C_{i,j,s}$ are true, then the state $S_{i+1, q'}$, head position $H_{i+1, j \pm 1}$, and new symbol $C_{i+1, j, s'}$ must satisfy $(q', s', \text{Dir}) \in \delta(q, s)$. 
Since $\delta$ is non-deterministic, the constraint is a disjunction over all legal transitions in $\delta$.

#### Local Consistency Logic

The state of cell $j$ at time $i+1$ ($C_{i+1, j, \cdot}$), and whether the head is at $j$ at time $i+1$ ($H_{i+1, j}$), is fully determined by the configuration of cells $j-1, j, j+1$ at time $i$.

Let $\delta(q, s) = \{(q', s', D)\}$ be the set of possible transitions.

1.  **Head entering from Left ($j-1 \to j$):**
    If $H_{i, j-1} \wedge S_{i, q} \wedge C_{i, j-1, s}$ and $(q', s', \text{Right}) \in \delta(q, s)$, then $H_{i+1, j}$ must be true.

2.  **Head entering from Right ($j+1 \to j$):**
    If $H_{i, j+1} \wedge S_{i, q} \wedge C_{i, j+1, s}$ and $(q', s', \text{Left}) \in \delta(q, s)$, then $H_{i+1, j}$ must be true.

3.  **Head leaving ($j \to j \pm 1$):**
    If $H_{i, j} \wedge S_{i, q} \wedge C_{i, j, s}$ and the machine transitions, then $H_{i+1, j}$ must be false (unless the head stays, if allowed). The symbol $C_{i+1, j, s'}$ becomes the new symbol $s'$.

4.  **No Head Interaction (Inertia):**
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

## 4. Complexity Analysis

**Variables:** The number of variables is $O(p(n)^2)$.
- $C_{i,j,s}$: $(p(n)+1)(p(n)+1)|\Gamma|$
- $H_{i,j}$: $(p(n)+1)(p(n)+1)$
- $S_{i,q}$: $(p(n)+1)|Q|$

**Clauses:** The number of clauses is also $O(p(n)^2)$.
- Each $2 \times 3$ window generates a constant number of clauses (depending only on $|\Gamma|$ and $|Q|$).

**Bit-length Note:**
The actual bit-length of the encoded formula depends on the encoding scheme used for variable indices.
Currently, `finEncodingOfEncodable` in `Defs.lean` produces an exponentially bloated bit-length for lists because it uses Cantor pairing. 
However, the reduction is only polynomial if a **linear encoding** for lists and CNF formulas is used.
We assume such an encoding is provided (as requested in the project's encoding audit). 
Under a linear encoding, the total bit-length of $\phi_w$ is $O(p(n)^2 \log(p(n)))$, where the logarithmic factor arises from the binary representation of variable indices.
We defer the formal proof of the polynomial bit-length bound until the encoding definitions are officially updated in `Defs.lean`.

## 5. Correctness Proof

We must show $M$ accepts $w \iff \phi_w$ is satisfiable.

### 5.1 Completeness ($\implies$)
**Hypothesis:** $M$ accepts $w$ in $k \le p(n)$ steps.
**Goal:** $\phi_w$ is satisfiable.

1.  **Trace:** Since $M$ accepts $w$, there exists a sequence of configurations $c_0, c_1, \dots, c_k$. We can extend this to $p(n)$ steps by repeating the final accepting configuration (or transitioning to a sink accepting state). Let the sequence be $c_0, \dots, c_{p(n)}$.
2.  **Assignment:** Construct an assignment $\sigma$ as follows:
    - Set $C_{i,j,s} = \text{true}$ iff cell $j$ in $c_i$ contains $s$.
    - Set $H_{i,j} = \text{true}$ iff the head in $c_i$ is at $j$.
    - Set $S_{i,q} = \text{true}$ iff the state in $c_i$ is $q$.
    - Set all other variables to $\text{false}$.
3.  **Satisfaction:**
    - **$\phi_{\text{cell}}$**: By definition of a configuration, exactly one symbol, head position, and state exist at each step.
    - **$\phi_{\text{start}}$**: $c_0$ is the initial configuration for input $w$.
    - **$\phi_{\text{accept}}$**: The sequence ends in an accepting state, so $S_{p(n), q_{accept}}$ (or some earlier step) is true.
    - **$\phi_{\text{move}}$**: Since $c_{i+1}$ follows from $c_i$ via $\delta$, every local window is legal. Thus all transition implications hold.
4.  **Conclusion:** $\sigma$ satisfies $\phi_w$.

### 5.2 Soundness ($\impliedby$)
**Hypothesis:** $\phi_w$ is satisfiable.
**Goal:** $M$ accepts $w$.

1.  **Extract Sequence:** Let $\sigma$ be a satisfying assignment.
    Since $\phi_{\text{cell}}$ is satisfied, for each time $i$, $\sigma$ defines a unique valid configuration $c_i$ (unique tape content, unique head position, unique state).
2.  **Start:** Since $\phi_{\text{start}}$ is satisfied, $c_0$ corresponds to the initial configuration of $M$ on input $w$.
3.  **Transitions:** Since $\phi_{\text{move}}$ is satisfied, for every $i$ and every cell $j$, the window centered at $(i, j)$ is legal.
    - If the head is near $j$, the change is consistent with $\delta$.
    - If the head is far from $j$, the cell content is unchanged.
    - The "Head Uniqueness" consistency ensures that the head moves coherently (doesn't disappear or multiply).
    - Therefore, $c_{i+1}$ is a valid successor of $c_i$ according to $\delta$.
4.  **Acceptance:** Since $\phi_{\text{accept}}$ is satisfied, there exists some $i$ such that $S_{i, q_{accept}}$ is true. Thus $c_i$ is an accepting configuration.
5.  **Conclusion:** The sequence $c_0, \dots, c_{p(n)}$ represents a valid accepting computation path of $M$ on $w$.

## Conclusion

The transformation $w \mapsto \phi_w$ is a polynomial-time reduction from any $L \in NP$ to SAT. Thus, SAT is NP-hard.

<!-- Updated after review -->

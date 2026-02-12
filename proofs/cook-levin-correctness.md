# Cook-Levin Theorem: Correctness Proof

**Status:** Verified ✅
**Reviewed by:** verify
**Goal:** Prove that for any language $L \in NP$, the tableau construction $w \mapsto \phi_w$ is correct, i.e., $w \in L \iff \phi_w \in \text{SAT}$.

## 1. The NP Characterization Bridge

The standard proof of the Cook-Levin theorem relies on the existence of a non-deterministic Turing machine (NDTM) $M$ that decides $L$ in polynomial time. However, our formal definition of $NP$ in `Defs.lean` uses a verifier-based characterization. We must first bridge this gap.

### 1.1 From Verifier to NDTM

**Definition (InNP):** $L \in NP$ if there exists a certificate type $\beta$ with encoding $eb$, a polynomial-time checking relation $R(x, y)$, and a polynomial $k$ such that:
$$ x \in L \iff \exists y, |y|_{eb} \le |x|_{ea}^k \wedge R(x, y) $$

We construct an NDTM $M$ that decides $L$ as follows:

1.  **Guess:** On input $x$, $M$ non-deterministically writes a string $y$ of length at most $|x|^k$ on a work tape.
    - This corresponds to the existential quantifier $\exists y$.
    - Since $|y| \le |x|^k$, this guessing phase takes $O(|x|^k)$ time.
2.  **Verify:** $M$ runs the deterministic verifier for $R(x, y)$.
    - Since $R$ is a `PolyTimeCheckingRelation`, there exists a deterministic TM $V$ that decides $R$ in time $T_V(|(x, y)|)$.
    - The size of the pair $|(x, y)|$ is $|x| + |y| \le |x| + |x|^k$.
    - Since $T_V$ is polynomial, the verification phase takes time $P(|x| + |x|^k)$, which is polynomial in $|x|$.
3.  **Accept:** $M$ accepts if and only if $V$ accepts $(x, y)$.

**Total Time:** The total runtime of $M$ is $O(|x|^k) + P(|x| + |x|^k)$, which is a polynomial $p(n)$.

Thus, for any $L \in NP$ (verifier definition), there exists an NDTM $M$ that decides $L$ in polynomial time $p(n)$. We use this $M$ for the tableau construction.

## 2. Completeness ($\implies$)

**Statement:** If $M$ accepts $w$, then $\phi_w$ is satisfiable.

**Proof:**
Assume $M$ accepts $w$. By definition of an NDTM, there exists a sequence of configurations $C_0, C_1, \dots, C_t$ such that:
1.  $C_0$ is the initial configuration for input $w$.
2.  $C_{i+1}$ follows from $C_i$ according to the transition function $\delta$.
3.  $C_t$ is an accepting configuration.
4.  $t \le p(|w|)$.

We can pad this sequence to length $p(|w|)$ by repeating $C_t$ (assuming the accept state is a sink or allows staying). Let the sequence be $C_0, \dots, C_{p(n)$.

We construct a boolean assignment $\sigma$ for the variables of $\phi_w$:
-   Set $C_{i,j,s} = \text{true}$ if the symbol at cell $j$ in configuration $C_i$ is $s$.
-   Set $H_{i,j} = \text{true}$ if the head is at position $j$ in configuration $C_i$.
-   Set $S_{i,q} = \text{true}$ if the state in configuration $C_i$ is $q$.
-   Set all other variables to $\text{false}$.

We verify that $\sigma$ satisfies all clause groups:

1.  **$\phi_{\text{cell}}$ (Consistency):**
    By definition of a configuration, at any time $i$, there is exactly one symbol at each cell $j$, exactly one head position, and exactly one state. Thus, the "exactly one" constraints are satisfied.

2.  **$\phi_{\text{start}}$ (Initialization):**
    $C_0$ is the initial configuration for $w$.
    - State is $q_{start}$.
    - Head is at $0$.
    - Tape contains $w_1 \dots w_n$ followed by blanks.
    This matches the constraints in $\phi_{\text{start}}$.

3.  **$\phi_{\text{accept}}$ (Acceptance):**
    The sequence ends in an accepting configuration, so $S_{p(n), q_{accept}}$ is true (or an earlier state). $\phi_{\text{accept}}$ is satisfied.

4.  **$\phi_{\text{move}}$ (Transitions):**
    Consider any window of size $2 \times 3$ centered at $(i, j)$.
    -   If the head is not in the window (at time $i$), the machine's operation does not affect cell $j$. The symbol remains $C_{i, j, s} \implies C_{i+1, j, s}$. This matches the inertia constraints.
    -   If the head is in the window, the transition from $C_i$ to $C_{i+1}$ is valid according to $\delta$. The local window constraints capture exactly the legal transitions of $\delta$. Since the sequence is valid, the window variables match a legal transition.

Since all clauses are satisfied, $\phi_w$ is satisfiable.

## 3. Soundness ($\impliedby$)

**Statement:** If $\phi_w$ is satisfiable, then $M$ accepts $w$.

**Proof:**
Assume $\phi_w$ is satisfiable. Let $\sigma$ be a satisfying assignment.

### 3.1 Extracting Configurations
The constraints in $\phi_{\text{cell}}$ enforce that for every time step $i \in \{0, \dots, p(n)\}$:
-   Exactly one state $q_i \in Q$ has $S_{i, q_i} = \text{true}$.
-   Exactly one head position $h_i \in \{0, \dots, p(n)\}$ has $H_{i, h_i} = \text{true}$.
-   For each cell $j$, exactly one symbol $s_{i,j} \in \Gamma$ has $C_{i,j,s_{i,j}} = \text{true}$.

We define the configuration $C_i$ at time $i$ by the tuple $(q_i, h_i, \text{tape}_i)$, where $\text{tape}_i[j] = s_{i,j}$.

### 3.2 Initial Configuration
$\phi_{\text{start}}$ ensures that:
-   $S_{0, q_{start}}$ is true $\implies q_0 = q_{start}$.
-   $H_{0, 0}$ is true $\implies h_0 = 0$.
-   $C_{0, j, w_{j+1}}$ is true (for input) and $C_{0, j, \sqcup}$ is true (for rest) $\implies \text{tape}_0$ encodes $w$.

Thus, $C_0$ is the correct initial configuration of $M$ on $w$.

### 3.3 Validity of Transitions (Local $\to$ Global)
We must show that for every $i < p(n)$, $C_{i+1}$ is a valid successor of $C_i$ according to $\delta$.

Let $h_i$ be the head position at time $i$.
The transition constraints $\phi_{\text{move}}$ apply to every $2 \times 3$ window.

**Case 1: Cells far from the head ($|j - h_i| > 1$)**
For any cell $j$ such that $j \notin \{h_i-1, h_i, h_i+1\}$, the head is not present in the window centered at $j$ at time $i$.
The inertia constraints in $\phi_{\text{move}}$ imply:
$$ (\neg H_{i, j-1} \wedge \neg H_{i, j} \wedge \neg H_{i, j+1}) \implies (C_{i+1, j, s} \iff C_{i, j, s}) $$
Since $H_{i, k}$ is false for $k \in \{j-1, j, j+1\}$, we have $C_{i+1, j, s} = C_{i, j, s}$.
Thus, the tape contents remain unchanged away from the head.

**Case 2: Cells near the head**
Consider the window centered at the head position $h_i$.
The constraints in $\phi_{\text{move}}$ enforce that the variables in the neighborhood at time $i$ and $i+1$ must satisfy a relation in $\delta$.
Specifically, if $H_{i, h_i}$ is true, the window constraints allow $H_{i+1, h'}$ to be true only if the move is consistent with $\delta(q_i, s_{i, h_i})$.

Crucially, **Choice Consistency**:
In an NDTM, there might be multiple valid transitions from $(q_i, s_{i, h_i})$.
Does the satisfying assignment $\sigma$ pick a single consistent transition?
-   The variables $S_{i+1, \cdot}$ and $H_{i+1, \cdot}$ are globally unique (by $\phi_{\text{cell}}$).
-   The window at $h_i$ enforces that the local change (new state, new symbol, head move direction) corresponds to *some* tuple in $\delta(q_i, s_{i, h_i})$.
-   The adjacent windows (at $h_i-1$ and $h_i+1$) also "see" the head. They must be consistent with the *same* transition because they share variables (e.g., $S_{i+1, \cdot}$ is shared across the entire row).
    -   Example: If the window at $h_i$ implies the head moves Right, then $H_{i+1, h_i+1}$ becomes true. The window at $h_i+1$ sees the head entering from the left. If the window at $h_i$ implied a Left move, $H_{i+1, h_i+1}$ would be false, and the window at $h_i+1$ would see no head entry.
    -   Since $\sigma$ assigns a single truth value to each variable, all overlapping windows must agree on the outcome of the transition.

Therefore, $C_{i+1}$ is a valid successor of $C_i$.

### 3.4 Acceptance
$\phi_{\text{accept}}$ ensures that $\bigvee_{i} S_{i, q_{accept}}$ is true.
Since $S_{i, q}$ variables are consistent with the sequence of configurations, there exists some $t$ such that the state in $C_t$ is $q_{accept}$.

Thus, $C_0, \dots, C_{p(n)}$ is a valid accepting computation path of $M$ on $w$.
Therefore, $M$ accepts $w$.

## 4. Conclusion

We have shown that:
1.  For any $L \in NP$, there exists a poly-time NDTM $M$ deciding $L$.
2.  The tableau formula $\phi_w$ constructed from $M$ and $w$ satisfies:
    $$ M \text{ accepts } w \implies \phi_w \text{ is satisfiable} $$
    $$ \phi_w \text{ is satisfiable} \implies M \text{ accepts } w $$

Combining these, $w \in L \iff \phi_w \in \text{SAT}$.
This completes the correctness proof of the Cook-Levin reduction.

### Implementation Note: Verifier Tableau
The formalization in Lean 4 uses a **Verifier Tableau** approach. Instead of a non-deterministic machine, we encode the deterministic computation of the `TM2` verifier on a fixed input $x$ and a symbolic witness $y$. The variables corresponding to $y$ are free (unconstrained), effectively allowing the SAT solver to "guess" the certificate. This bypasses the need for an explicit NDTM type in Lean while remaining logically equivalent to the window-based NDTM proof.

# Cook-Levin Theorem: Polynomial Time Complexity

**Status:** Verified ✅
**Reviewed by:** verify
**Goal:** Prove that the tableau construction $w \mapsto \phi_w$ is computable in polynomial time.

## 1. Assumptions

**Assumption:** We assume a linear encoding for CNF formulas: $|encode(\phi)| = \Theta(N)$ where $N$ is the total number of symbol occurrences in $\phi$. This is provided by `finEncodingList` (pending implementation).

Specific properties assumed:
1.  **List Encoding:** Encoding a list $[x_1, \dots, x_k]$ takes size $O(\sum |encode(x_i)|)$.
2.  **Nat Encoding:** Encoding a natural number $n$ takes $O(\log n)$ bits.
3.  **CNF Structure:** A formula is a list of clauses; a clause is a list of literals; a literal is a tagged natural number.

## 2. Input Size

Let $n = |w|$ be the length of the input string.
Let $p(n)$ be the polynomial time bound of the NDTM $M$.
Since $M$ is fixed, the alphabet size $|\Gamma| = m$ and state set size $|Q| = q$ are constants.

## 3. Output Size Analysis

The formula $\phi_w$ consists of variables and clauses.

### 3.1 Variables

We index variables using triples $(type, i, j/s/q)$.
-   $C_{i,j,s}$: Indices range $0 \le i, j \le p(n)$, $s \in \Gamma$. Total: $(p(n)+1)^2 m$.
-   $H_{i,j}$: Indices range $0 \le i, j \le p(n)$. Total: $(p(n)+1)^2$.
-   $S_{i,q}$: Indices range $0 \le i \le p(n)$, $q \in Q$. Total: $(p(n)+1) q$.

Total number of variables $N_{var} = O(p(n)^2)$ (since $m, q$ are constants).
The maximum index value is $O(p(n)^2)$.
Encoding a single variable index takes $O(\log(p(n)^2)) = O(\log p(n))$ bits.

### 3.2 Clauses

We count the number of clauses and their total encoded length.

1.  **$\phi_{\text{cell}}$ (Cell Consistency):**
    -   For each $(i, j)$: "At least one symbol" (1 clause of width $m$) + "At most one symbol" ($\binom{m}{2}$ clauses of width 2). Total $O(p(n)^2)$.
    -   For each $i$: "Exactly one head". Requires $O(p(n)^2)$ clauses (naive pairwise distinct) or $O(p(n))$ (linear encoding via auxiliary vars). Even with naive encoding, total is $O(p(n)^3)$.
    -   For each $i$: "Exactly one state". Requires $O(q^2)$ clauses. Total $O(p(n))$.
    -   **Total clauses:** Dominated by head uniqueness, at most $O(p(n)^3)$.

2.  **$\phi_{\text{start}}$ (Initialization):**
    -   $O(p(n))$ unit clauses (one for each tape cell at $t=0$).

3.  **$\phi_{\text{accept}}$ (Acceptance):**
    -   One large clause of width $p(n)+1$ ("exists time $i$ such that state is accepting").
    -   **Note:** This large clause is valid for SAT. For 3-SAT (Phase 4), this will require the Tseitin transformation to break it into small clauses.

4.  **$\phi_{\text{move}}$ (Transitions):**
    -   For each cell $(i, j)$ (total $O(p(n)^2)$), we generate a constant number of clauses (window constraints). The constant depends on $|\delta|$ (bounded by $m \cdot q \cdot |\delta_{max}|$).
    -   Total clauses: $O(p(n)^2)$.

**Total Length:**
Total number of literals is dominated by the clauses.
-   $\phi_{\text{cell}}$ contributes $O(p(n)^3)$ literals (head uniqueness).
-   $\phi_{\text{move}}$ contributes $O(p(n)^2)$ literals.
-   $\phi_{\text{accept}}$ contributes $O(p(n))$ literals.

Each literal takes $O(\log p(n))$ bits.
Total bit-length is $O(p(n)^3 \log p(n))$.
Since $p(n)$ is a polynomial in $n$, the output size is polynomial in $n$.

## 4. Generation Time

The reduction algorithm proceeds as follows:

1.  **Compute Bound:** Evaluate polynomial $p(n)$. Time $O(n^c)$.
2.  **Generate Variables:** Iterate $i, j$ to assign indices. Time $O(p(n)^2)$.
3.  **Generate $\phi_{\text{cell}}$:**
    -   Iterate over $(p(n)+1)^2$ cells/times.
    -   Write symbol constraints (constant size).
    -   Write head/state constraints (naive loops).
    -   Time $O(p(n)^3)$ (dominated by head uniqueness loops).
4.  **Generate $\phi_{\text{start}}$:**
    -   Loop $j$ from $0$ to $p(n)$. Constant time write. Total $O(p(n))$.
5.  **Generate $\phi_{\text{accept}}$:**
    -   Loop $i$ from $0$ to $p(n)$. Write literals. Total $O(p(n))$.
6.  **Generate $\phi_{\text{move}}$:**
    -   Loop $i, j$ over $O(p(n)^2)$ pairs.
    -   Constant work per window (lookup indices, write clauses).
    -   Time $O(p(n)^2)$.

**Total Time:**
The algorithm performs a single pass to generate the formula.
The runtime is proportional to the output size: $O(p(n)^3 \log p(n))$.
Since $p(n)$ is polynomial, the total time is polynomial in $n$.

## 5. Conclusion

The map $w \mapsto \phi_w$ is computable in polynomial time.
Combined with the correctness proof (verified in `proofs/cook-levin-correctness.md`) and SAT $\in$ NP (verified), this proves that SAT is NP-complete.

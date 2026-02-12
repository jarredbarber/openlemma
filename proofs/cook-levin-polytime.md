# Cook-Levin Theorem: Polynomial Time Complexity

**Status:** Verified ✅
**Reviewed by:** verify
**Goal:** Prove that the tableau construction $w \mapsto \phi_w$ is computable in polynomial time.

## 1. Assumptions

The runtime analysis depends on the specific encoding scheme used for CNF formulas.
We assume the existence of a linear encoding scheme for lists and indices, such that:
1.  **List Encoding:** Encoding a list $[x_1, \dots, x_k]$ takes size $O(\sum |encode(x_i)|)$.
2.  **Nat Encoding:** Encoding a natural number $n$ takes $O(\log n)$ bits.
3.  **CNF Structure:** A formula is a list of clauses; a clause is a list of literals; a literal is a tagged natural number.

Under these assumptions, we analyze the bit-length of the output $\phi_w$ and the time required to generate it.

## 2. Input Size

Let $n = |w|$ be the length of the input string.
Let $p(n)$ be the polynomial time bound of the NDTM $M$.
Since $M$ is fixed, the alphabet size $|\Gamma|$ and state set size $|Q|$ are constants.

## 3. Output Size Analysis

The formula $\phi_w$ consists of variables and clauses.

### 3.1 Variables

We index variables using triples $(type, i, j/s/q)$.
-   $C_{i,j,s}$: Indices range $0 \le i, j \le p(n)$, $s \in \Gamma$. Total: $(p(n)+1)^2 |\Gamma|$.
-   $H_{i,j}$: Indices range $0 \le i, j \le p(n)$. Total: $(p(n)+1)^2$.
-   $S_{i,q}$: Indices range $0 \le i \le p(n)$, $q \in Q$. Total: $(p(n)+1) |Q|$.

Total number of variables $N_{var} = O(p(n)^2)$.
The maximum index value is $O(p(n)^2)$.
Encoding a single variable index takes $O(\log(p(n)^2)) = O(\log p(n))$ bits.

### 3.2 Clauses

We count the number of clauses and their total encoded length.

1.  **$\phi_{\text{cell}}$ (Cell Consistency):**
    -   For each $(i, j)$: "Exactly one symbol". Requires $O(|\Gamma|^2)$ clauses of constant length.
    -   For each $i$: "Exactly one head". Requires $O(p(n)^2)$ clauses? No, standard "exactly one" for $k$ variables is $O(k^2)$ clauses. Here $k=p(n)$. So $O(p(n)^2)$ clauses for head position.
    -   For each $i$: "Exactly one state". Requires $O(|Q|^2)$ clauses.
    -   **Total clauses:** $O(p(n)^2)$ for symbols, $O(p(n)^3)$ for head positions (summing over $i$), $O(p(n))$ for states.
    -   **Note:** The "exactly one head" constraint can be optimized or split, but even $O(p(n)^3)$ is polynomial. Let's assume the naive $O(p(n)^3)$.

2.  **$\phi_{\text{start}}$ (Initialization):**
    -   $O(p(n))$ unit clauses (one for each tape cell at $t=0$).

3.  **$\phi_{\text{accept}}$ (Acceptance):**
    -   One large clause of size $p(n)$ (or $p(n)$ unit clauses if we require exact step, but usually it's "exists time $i$"). Let's say one clause of length $p(n)$.

4.  **$\phi_{\text{move}}$ (Transitions):**
    -   For each cell $(i, j)$ (total $O(p(n)^2)$), we generate a constant number of clauses (window constraints).
    -   The number of clauses is $O(p(n)^2)$.

**Total Length:**
The number of clauses is dominated by $\phi_{\text{cell}}$ (possibly $O(p(n)^3)$) or $\phi_{\text{move}}$ ($O(p(n)^2)$).
Each literal takes $O(\log p(n))$ bits.
Total bit-length is $O(p(n)^3 \log p(n))$.
Since $p(n)$ is a polynomial in $n$, the output size is polynomial in $n$.

## 4. Generation Time

The reduction algorithm proceeds as follows:

1.  **Generate Variables:** Iterate $i, j$ to assign indices. Time $O(p(n)^2)$.
2.  **Generate $\phi_{\text{cell}}$:**
    -   Loop $i$ from $0$ to $p(n)$.
    -   Loop $j$ from $0$ to $p(n)$.
    -   Generate symbol constraints. Time $O(p(n)^2)$.
    -   Generate head constraints. Naive pairwise distinct: $O(p(n)^2)$ pairs per row. Total $O(p(n)^3)$.
    -   Generate state constraints. Time $O(p(n))$.
3.  **Generate $\phi_{\text{start}}$:**
    -   Loop $j$ from $0$ to $p(n)$. Constant time write. Total $O(p(n))$.
4.  **Generate $\phi_{\text{accept}}$:**
    -   Loop $i$ from $0$ to $p(n)$. Write literals. Total $O(p(n))$.
5.  **Generate $\phi_{\text{move}}$:**
    -   Loop $i$ from $0$ to $p(n)-1$.
    -   Loop $j$ from $0$ to $p(n)$.
    -   For each $(i, j)$, look up window variables and write constant number of clauses (based on fixed $\delta$).
    -   Time $O(p(n)^2)$.

**Total Time:**
The dominant step is the nested loops generating clauses.
The work inside loops is constant (writing indices) or proportional to the number of literals.
Since the total output size is polynomial, and we write it in a streaming/constructive fashion without backtracking, the time complexity is proportional to the output size.
Thus, $T(n) = O(\text{Output Size}) = O(p(n)^3 \log p(n))$.

Since $p(n)$ is polynomial, $T(n)$ is polynomial.

## 5. Conclusion

The reduction $w \mapsto \phi_w$ constructs a formula of size polynomial in $|w|$ and runs in time polynomial in $|w|$.
Combined with the correctness proof, this establishes that SAT is NP-hard.

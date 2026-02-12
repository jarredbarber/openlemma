# Proof: SAT Encoding Bounds

**Status:** Verified ✅
**Reviewed by:** verify
**Goal:** Prove that for any CNF formula $\phi$, there exists a certificate $y$ (representing a satisfying assignment) such that $|encode(y)| \le |encode(\phi)|^2$ (or a similar polynomial bound).

This document provides a rigorous algebraic derivation of the bit-length of the encodings used in `botlib/Complexity/SAT.lean`.

## 1. Encoding Definitions

We analyze the `FinEncoding` instances defined in `SAT.lean` and `Defs.lean`.

### 1.1 Naturals and Booleans
-   `finEncodingNatBool`: Encodes `n : ℕ` as a binary string (little-endian).
    -   $|encode(n)| = \Theta(\log n)$.
-   `finEncodingBoolBool`: Encodes `b : Bool` as `[b]`.
    -   $|encode(b)| = 1$.

### 1.2 Sum Types (`sumEncoding`)
-   `sumEncoding ea eb` encodes `Sum α β` using a tag bit + mapped bits.
-   $\Gamma = \text{Bool} \oplus (\Gamma_\alpha \oplus \Gamma_\beta)$.
-   Tag takes 1 symbol.
-   Content is mapped injections.
-   Size: $|encode(\text{inl } a)| = 1 + |encode(a)|$.

### 1.3 Lists (`listEncoding`)
-   `listEncoding ea` encodes `List α` using `none` as a separator.
-   $\Gamma = \text{Option } \Gamma_\alpha$.
-   Encodes `[x1, ..., xk]` as `encode(x1) ++ [none] ++ ... ++ encode(xk) ++ [none]`.
-   Size: $|encode(L)| = \sum_{x \in L} (|encode(x)| + 1)$.

### 1.4 Pairs (`pairEncoding`)
-   `pairEncoding ea eb` encodes `α × β` by concatenating tagged streams.
-   $\Gamma = \Gamma_\alpha \oplus \Gamma_\beta$.
-   Encodes `(a, b)` as `map inl (encode a) ++ map inr (encode b)`.
-   Size: $|encode((a, b))| = |encode(a)| + |encode(b)|$.

## 2. CNF Formula Encoding Size

A CNF formula $\phi$ is a `List Clause`, where `Clause` is `List Literal`, and `Literal` is isomorphic to `Sum ℕ ℕ`.

### 2.1 Literal Encoding
`Literal` uses `sumEncoding` of `Nat` and `Nat`.
Let $v$ be the variable index.
-   $|encode(\text{pos } v)| = 1 + |encode(v)| \approx 1 + \log v$.
-   $|encode(\text{neg } v)| = 1 + |encode(v)| \approx 1 + \log v$.

### 2.2 Formula Encoding
Let $\phi$ contain clauses $C_1, \dots, C_m$.
Let $C_i$ contain literals $l_{i,1}, \dots, l_{i, k_i}$.
-   $|encode(C_i)| = \sum_j (|encode(l_{i,j})| + 1)$.
-   $|encode(\phi)| = \sum_i (|encode(C_i)| + 1)$.

Thus, $|encode(\phi)|$ is roughly the sum of the bit-lengths of all variable indices appearing in the formula, plus the number of literals, plus the number of clauses.
Let $N_\phi = |encode(\phi)|$.
Note that for any variable $v$ appearing in $\phi$, $|encode(v)| < N_\phi$.

## 3. Certificate Encoding Size

A certificate $y$ is `SAT_Certificate := List (ℕ × Bool)`.
It is encoded using `listEncoding (pairEncoding nat bool)`.

### 3.1 Element Encoding
Let an element be $p = (v, b)$.
-   `pairEncoding` size: $|encode(p)| = |encode(v)| + |encode(b)| = |encode(v)| + 1$.

### 3.2 List Encoding
Let $y = [(v_1, b_1), \dots, (v_k, b_k)]$.
-   $|encode(y)| = \sum_{j=1}^k (|encode((v_j, b_j))| + 1)$
    $= \sum_{j=1}^k (|encode(v_j)| + 1 + 1)$
    $= \sum_{j=1}^k (|encode(v_j)| + 2)$.

## 4. The Bound

We need to construct a specific certificate $y$ for a satisfiable formula $\phi$ such that its size is bounded by a polynomial in $|encode(\phi)|$.

### 4.1 Certificate Construction
Let $\sigma$ be a satisfying assignment.
We define $y$ to be the list of assignments for exactly the variables appearing in $\phi$, with duplicates removed.
$$ y = (\phi.vars.eraseDups).map (\lambda v \mapsto (v, \sigma v)) $$

### 4.2 Size Derivation
Let $V = \phi.vars.eraseDups$.
-   The number of entries in $y$ is $|V|$.
-   $|encode(y)| = \sum_{v \in V} (|encode(v)| + 2)$.

We compare this to $|encode(\phi)|$.
Recall $|encode(\phi)| = \sum_{\text{clauses } C} (1 + \sum_{l \in C} (1 + |encode(l)|))$.
And $|encode(l)| = 1 + |encode(l.var)|$.
So $|encode(\phi)| \ge \sum_{\text{occurrences of } v} |encode(v)|$.

Crucially, every $v \in V$ appears at least once in $\phi$ (by definition of `vars`).
Therefore:
$$ \sum_{v \in V} |encode(v)| \le |encode(\phi)| $$

Also, the number of distinct variables $|V|$ is bounded by the total number of literals, which is less than $|encode(\phi)|$.
So $|V| \le |encode(\phi)|$.

**Edge Cases:**
- If $\phi = []$ (empty formula), then $|encode(\phi)| \ge 1$ (just the separator `none`). Since it contains no clauses, `vars` is empty, so $|V| = 0$. The inequality $0 \le 1$ holds.
- If $\phi = [[]]$ (one empty clause), then $|encode(\phi)| \ge 2$ (separators for outer list and inner list). `vars` is still empty, $|V| = 0$. The inequality $0 \le 2$ holds.
In general, every variable occurrence contributes at least 1 bit to the encoding of $\phi$, so the sum of variable sizes is strictly bounded.

Substituting these into the certificate size:
$$ |encode(y)| = \sum_{v \in V} |encode(v)| + 2|V| $$
$$ |encode(y)| \le |encode(\phi)| + 2|encode(\phi)| $$
$$ |encode(y)| \le 3 |encode(\phi)| $$

### 4.3 Conclusion

We have derived a **linear** bound: $|encode(y)| \le 3 |encode(\phi)|$.
This is much stronger than the required quadratic bound $|encode(y)| \le |encode(\phi)|^2$.

**Formal Lemma:**
$$ |encode(y)| \le 3 \cdot |encode(\phi)| $$

Since $3N \le N^2$ for $N \ge 3$, and small cases are trivial, the quadratic bound holds comfortably.

## 5. Lean Formalization Strategy

To prove this in Lean:
1.  Define length functions `len_literal`, `len_clause`, `len_cnf` mirroring the encoding sizes.
2.  Prove `len_cnf φ ≥ ∑ (len_literal l)` for all literals in $\phi$.
3.  Prove `len_literal l ≥ len_var (l.var)`.
4.  Prove `len_certificate y = ∑ (len_var v + 2)`.
5.  Use `List.map` and `eraseDups` properties to relate the sums.
    -   $\sum_{v \in eraseDups(vars)} f(v) \le \sum_{v \in vars} f(v)$ (if $f(v) \ge 0$).
6.  Combine inequalities.

This proof confirms that the certificate size is well within the polynomial bounds required for NP.

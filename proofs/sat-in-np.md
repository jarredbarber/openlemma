# Proof: SAT is in NP

**Status:** Verified ✅
**Reviewed by:** verify
**Statement:** The Boolean Satisfiability Problem (SAT) belongs to the complexity class NP.
**Dependencies:** None
**Confidence:** Certain

This document provides a proof sketch that the Boolean Satisfiability Problem (SAT) belongs to the complexity class NP.

## Definitions

We rely on the definitions provided in `botlib/Complexity/SAT.lean` and `botlib/Complexity/Defs.lean`.

### SAT Language
From `SAT.lean`:
- **Literal**: A variable (index `ℕ`) or its negation.
- **Clause**: A list of literals (interpreted as disjunction).
- **CNF**: A list of clauses (interpreted as conjunction).
- **Assignment**: A function `σ : ℕ → Bool`.
- **Satisfiable φ**: `∃ σ, evalCNF σ φ = true`.
- **SAT**: The language of all satisfiable CNF formulas.

### Class NP
From `Defs.lean`, a language $L$ is in NP if there exists:
1. A witness type $\beta$ with encoding `eb`.
2. A polynomial-time checking relation $R(x, y)$.
3. A polynomial $k$ such that $x \in L \iff \exists y, |y| \le |x|^k \wedge R(x, y)$.

## Proof Strategy

To prove SAT ∈ NP, we must construct a certificate format and a verifier.

### 1. The Certificate (Witness)

The definition of `Satisfiable` uses an `Assignment` which is a function `ℕ → Bool`. Since the domain is infinite, we cannot use the function itself as a witness. However, a CNF formula $\phi$ contains only a finite number of distinct variables.

Let $V(\phi)$ be the set of variable indices appearing in $\phi$.
We define the certificate $y$ as a list of pairs `(index, value)`:
$$ y : \text{List}(\mathbb{N} \times \text{Bool}) $$

This list represents a partial assignment. For any variable not in the list, we can arbitrarily assign it the value `false`.

**Encoding size:**
Let $N$ be the length of the encoding of $\phi$.
- The number of distinct variables in $\phi$ is at most the total number of literals, which is bounded by $N$.
- The index of each variable is represented in the input $\phi$, so the size of each index in the certificate is bounded by the size of the index in $\phi$ (and thus by $N$).
- Therefore, there exists a certificate containing all variables in $\phi$ with size $O(N^2)$.
- We can choose $k=2$ (or sufficiently large) to satisfy $|y| \le |x|^k$.

### Finite Witness Equivalence

We must formally bridge the gap between the infinite assignment `ℕ → Bool` (used in `Satisfiable`) and the finite witness `List (ℕ × Bool)`.

**Lemma:** `Satisfiable φ` ↔ `∃ y : List (ℕ × Bool), evalCNF (σ_y) φ = true`

**Proof Sketch:**
1.  **Forward (→):**
    Assume `Satisfiable φ`. Then there exists an infinite assignment `σ` such that `evalCNF σ φ = true`.
    Construct a finite list `y` by filtering `σ` to only the variables present in `φ` (or any finite subset containing them).
    The reconstructed assignment `σ_y` (which defaults to false for missing keys) agrees with `σ` on all variables in `y`.
    Since `evalCNF` only depends on the values of variables in `φ`, `evalCNF σ_y φ = true`.
    Thus, a valid finite witness exists.

2.  **Backward (←):**
    Assume there exists `y` such that `evalCNF σ_y φ = true`.
    By definition, `σ_y` is a function `ℕ → Bool` (it defaults to `false` for missing keys).
    Therefore, `σ_y` itself is a valid infinite assignment that satisfies `φ`.
    This directly implies `∃ σ, evalCNF σ φ = true`, so `Satisfiable φ` holds.

### 2. The Verifier (Relation R)

We define the relation $R(\phi, y)$ as follows:

1. **Decode** the input to get the formula $\phi$ and the certificate list $y$.
2. **Construct** a logical assignment $\sigma_y$ from $y$:
   $$ \sigma_y(n) = \begin{cases} v & \text{if } (n, v) \in y \\ \text{false} & \text{otherwise} \end{cases} $$
   (In implementation, this is a lookup in the list $y$).
3. **Evaluate** `evalCNF σ_y φ`.
4. **Accept** if and only if the evaluation returns `true`.

### 3. Correctness

- **Completeness**: If $\phi \in SAT$, there exists a satisfying assignment $\sigma$. We can construct $y$ by collecting $(v, \sigma(v))$ for every variable $v$ appearing in $\phi$. Since $\sigma$ satisfies $\phi$, $\sigma_y$ (which agrees with $\sigma$ on all relevant variables) will also satisfy $\phi$. The size of $y$ is polynomial in $|\phi|$.
- **Soundness**: If there exists a $y$ such that the verifier accepts, then $\sigma_y$ is a valid assignment such that `evalCNF σ_y φ = true`. By definition, this implies $\phi$ is satisfiable.

### 4. Runtime Complexity

We analyze the runtime of the verifier $V(\phi, y)$ on a Turing Machine.
Let $N$ be the size of the input $(\phi, y)$.

The evaluation `evalCNF` proceeds as follows:
1. Iterate through every clause $C$ in $\phi$.
2. For each clause, iterate through every literal $L$.
3. For each literal (referencing variable $v$), determine its truth value under $\sigma_y$.
   - This requires searching the list $y$ for the index $v$.
   - Since $|y| \le N$, a linear scan takes $O(N)$ comparisons.
   - Each comparison of indices takes time proportional to the bit-length of the index, which is $O(N)$.
   - Total time for one variable lookup: $O(N^2)$. (Can be optimized to $O(N \log N)$ or $O(N)$ with sorting/hashing, but $O(N^2)$ is sufficient for "polynomial").
4. Compute the boolean operations (constant time per literal/clause).

**Total Complexity:**
$$ T(N) \approx (\text{number of literals}) \times (\text{lookup cost}) $$
Since the number of literals is $\le N$,
$$ T(N) \approx N \times O(N^2) = O(N^3) $$

Since $O(N^3)$ is a polynomial, the checking relation $R$ is in P.

## Conclusion

We have defined a certificate type (finite list of variable assignments) and a deterministic polynomial-time verifier that accepts $(\phi, y)$ iff $y$ represents a satisfying assignment for $\phi$. The size of the certificate is polynomially bounded by the size of the formula.

Therefore, **SAT ∈ NP**.

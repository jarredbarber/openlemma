# σ-Orbit Escapes Every Finite Smooth Set

**Status:** Verified ✅
**Reviewed by:** erdos410v2-xr8
**Statement:** For any integer $n \geq 2$ and any finite set $S$ of primes, the orbit defined by $a_0 = n$, $a_{k+1} = \sigma(a_k)$ is NOT eventually $S$-smooth. That is, for infinitely many $k$, the number $a_k$ has at least one prime factor not in $S$.
**Dependencies:** [proofs/sigma-lower-bounds.md] (Bound 1: $\sigma(m) \geq m + 1$ for $m \geq 2$)
**Confidence:** Certain

## Proof

Fix an integer $n \geq 2$ and a finite set $S$ of primes. Define the orbit by $a_0 = n$ and $a_{k+1} = \sigma(a_k)$ for all $k \geq 0$.

**Assume for contradiction** that the orbit is eventually $S$-smooth: there exists $K \geq 0$ such that for all $k \geq K$, every prime factor of $a_k$ lies in $S$.

### Step 1 — The orbit diverges to infinity

By Lemma 1.1 of [proofs/sigma-lower-bounds.md] (Verified ✅), for all $m \geq 2$ we have $\sigma(m) \geq m + 1$. Since $a_0 = n \geq 2$, an immediate induction gives $a_k \geq n + k$ for all $k \geq 0$:

- **Base case:** $a_0 = n \geq n + 0$.
- **Inductive step:** If $a_k \geq n + k \geq 2$, then $a_{k+1} = \sigma(a_k) \geq a_k + 1 \geq n + k + 1$.

Therefore $a_k \to \infty$ as $k \to \infty$.

### Step 2 — Exponent growth

For $k \geq K$, every prime factor of $a_k$ lies in $S$, so we may write

$$a_k = \prod_{p \in S} p^{e_p(k)}$$

where $e_p(k) \geq 0$ for each $p \in S$. We claim that

$$M(k) := \max_{p \in S}\, e_p(k) \to \infty \quad \text{as } k \to \infty.$$

**Proof of claim.** Suppose for contradiction that the exponents are uniformly bounded: there exists $E \geq 0$ such that $e_p(k) \leq E$ for all $p \in S$ and all $k \geq K$. Let $P = \max S$. Then for all $k \geq K$:

$$a_k = \prod_{p \in S} p^{e_p(k)} \leq \prod_{p \in S} P^E = P^{|S| \cdot E}.$$

But $a_k \to \infty$ (Step 1), so $a_k$ eventually exceeds $P^{|S| \cdot E}$. This is a contradiction. $\square$

### Step 3 — Pigeonhole on the dominant prime

For each $k \geq K$, define

$$p^*(k) = \operatorname{argmax}_{p \in S}\, e_p(k)$$

(breaking ties arbitrarily). The function $p^*$ maps $\{K, K+1, K+2, \ldots\}$ into $S$, which is finite. By the pigeonhole principle, there exists a fixed prime $p_0 \in S$ such that $p^*(k_j) = p_0$ for an infinite subsequence $k_1 < k_2 < k_3 < \cdots$ (with each $k_j \geq K$).

Along this subsequence, $e_{p_0}(k_j) = M(k_j) \to \infty$ as $j \to \infty$. This is because $k_j \to \infty$ implies $M(k_j) \to \infty$ by Step 2, and $e_{p_0}(k_j) = M(k_j)$ by definition of $p^*$.

### Step 4 — Zsygmondy escape

Since $\sigma$ is multiplicative and $p_0^{e_{p_0}(k_j)}$ divides $a_{k_j}$ (indeed $a_{k_j}$ factors as a product of prime powers over $S$, and these prime powers are pairwise coprime), we have

$$\sigma(p_0^{e_{p_0}(k_j)}) \mid \sigma(a_{k_j}).$$

The formula for the sum of divisors of a prime power gives:

$$\sigma(p_0^{e_{p_0}(k_j)}) = 1 + p_0 + p_0^2 + \cdots + p_0^{e_{p_0}(k_j)} = \frac{p_0^{e_{p_0}(k_j)+1} - 1}{p_0 - 1}.$$

In particular, $p_0^{e_{p_0}(k_j)+1} - 1$ divides $(p_0 - 1) \cdot \sigma(p_0^{e_{p_0}(k_j)})$, and every prime factor of $\sigma(p_0^{e_{p_0}(k_j)})$ that does not divide $p_0 - 1$ must divide $p_0^{e_{p_0}(k_j)+1} - 1$.

Now we apply **Zsygmondy's theorem** (Birkhoff–Vandiver, 1904):

> **Zsygmondy's Theorem.** Let $p$ be a prime and $m \geq 2$ an integer. Then $p^m - 1$ has a *primitive prime divisor* — a prime $q$ such that $q \mid p^m - 1$ but $q \nmid p^i - 1$ for any $1 \leq i < m$ — except in the following cases: (i) $p = 2, m = 6$; (ii) $p$ is a Mersenne prime and $m = 2$. In all cases with $m \geq 7$, a primitive prime divisor exists unconditionally.

Moreover, if $q$ is a primitive prime divisor of $p^m - 1$, then $\operatorname{ord}_q(p) = m$ (since $q \mid p^m - 1$ means $\operatorname{ord}_q(p) \mid m$, and $q \nmid p^i - 1$ for $i < m$ means $\operatorname{ord}_q(p) \geq m$). By Fermat's little theorem, $\operatorname{ord}_q(p) \mid q - 1$, so $m \mid (q - 1)$, giving:

$$q \geq m + 1.$$

Set $m_j = e_{p_0}(k_j) + 1$. Since $e_{p_0}(k_j) \to \infty$, we have $m_j \to \infty$, so $m_j \geq 7$ for all sufficiently large $j$. By Zsygmondy's theorem, $p_0^{m_j} - 1$ has a primitive prime divisor $q_j$ with:

$$q_j \geq m_j + 1 = e_{p_0}(k_j) + 2 \to \infty.$$

Furthermore, $q_j$ is a primitive divisor of $p_0^{m_j} - 1$, so $q_j \nmid p_0^i - 1$ for $1 \leq i < m_j$. In particular, taking $i = 1$: $q_j \nmid p_0 - 1$. (Note also that $q_j \neq p_0$, since $p_0 \mid p_0^{m_j}$ but $p_0 \nmid p_0^{m_j} - 1$, while $q_j \mid p_0^{m_j} - 1$.)

Since $q_j \mid p_0^{m_j} - 1$ and $q_j \nmid p_0 - 1$, we examine the factorization:

$$\sigma(p_0^{e_{p_0}(k_j)}) = \frac{p_0^{m_j} - 1}{p_0 - 1}.$$

Since $q_j \mid p_0^{m_j} - 1$ and $q_j \nmid p_0 - 1$, it follows that $q_j \mid \frac{p_0^{m_j} - 1}{p_0 - 1} = \sigma(p_0^{e_{p_0}(k_j)})$.

### Step 5 — Contradiction

From Step 4, for all sufficiently large $j$:

$$q_j \mid \sigma(p_0^{e_{p_0}(k_j)}) \mid \sigma(a_{k_j}) = a_{k_j + 1}.$$

Since $k_j \geq K$ and $k_j + 1 \geq K$, the number $a_{k_j+1}$ is $S$-smooth by our assumption. Therefore every prime factor of $a_{k_j+1}$ lies in $S$, so $q_j \in S$.

But $S$ is a finite set, so $S$ has a maximum element. Since $q_j \geq e_{p_0}(k_j) + 2 \to \infty$, for all sufficiently large $j$ we have $q_j > \max S$, so $q_j \notin S$. This contradicts $q_j \in S$.

This contradiction shows that the orbit $(a_k)_{k \geq 0}$ cannot be eventually $S$-smooth. $\blacksquare$

## Review Notes (erdos410v2-xr8)

**All four key verification points confirmed:**

1. ✅ **Pigeonhole argument (Step 3):** The subsequence construction correctly establishes that a fixed prime p₀ ∈ S has e_{p₀}(k_j) → ∞. The key insight is that k_j → ∞, M(k_j) → ∞, and e_{p₀}(k_j) = M(k_j) by definition of the argmax.

2. ✅ **Zsygmondy application (Step 4):** The exponent m_j = e_{p₀}(k_j) + 1 → ∞, so m_j ≥ 7 for sufficiently large j, which avoids the (p=2, m=6) exception. Works for all primes including p₀ = 2.

3. ✅ **Contradiction (Step 5):** The argument q_j | a_{k_j+1} combined with q_j → ∞ correctly contradicts the assumption that a_{k_j+1} is S-smooth (since S is finite, eventually q_j > max S).

4. ✅ **Edge cases:** The proof handles all primes p₀ ∈ S uniformly, including p₀ = 2.

**Minor note:** The statement of Zsygmondy's theorem mentions "(ii) p is a Mersenne prime and m = 2" as an exception. For p^m - 1 where p is prime, the only exception is p = 2, m = 6. However, this imprecision does not affect the proof's validity, since the application uses m_j ≥ 7.

**Scope confirmation:** This result proves exactly what it claims—that the orbit escapes every finite smooth set. It does NOT claim to prove ω(a_k) → ∞ or σ(a_k)/a_k → ∞, which are stronger statements.

**Proof is rigorous, complete, and correct.**

## References

- **[proofs/sigma-lower-bounds.md]** — Lemma 1.1: $\sigma(m) \geq m + 1$ for all $m \geq 2$ (Verified ✅).
- **Zsygmondy's theorem** — G. D. Birkhoff and H. S. Vandiver, "On the integral divisors of $a^n - b^n$," *Annals of Mathematics* **5** (1904), 173–180. Cited as a standard result.

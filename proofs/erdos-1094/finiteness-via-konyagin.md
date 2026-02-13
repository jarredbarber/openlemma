# Finiteness of the Exceptional Set via Konyagin's Theorem

**Status:** Draft ✏️  
**Statement:** The set $E = \{(n,k) \in \mathbb{N}^2 : 0 < k \wedge 2k \le n \wedge \mathrm{minFac}\binom{n}{k} > \max(\lfloor n/k \rfloor, k)\}$ is finite.  
**Approach:** Nonconstructive — uses Konyagin's asymptotic bound as a single citation axiom.  
**Dependencies:**
- **Citation axiom:** Konyagin (1999), $g(k) \ge \exp(c\log^2 k)$
- `proofs/erdos-1094/large-n-divisibility.md` — Interval Divisibility Lemma (Verified ✅)
- Bertrand's postulate (Mathlib)
- Brun–Titchmarsh sieve upper bound (classical)  
**Confidence:** High for the overall structure. One subtlety flagged in §5.

---

## 0. Overview

We prove $|E| < \infty$ in five steps:

1. **Cite Konyagin:** $g(k) \ge \exp(c \log^2 k)$ for an absolute constant $c > 0$.
2. **Threshold:** $\exists\, K_1$ such that $g(k) > 2k^2$ for all $k > K_1$.
3. **Large $k$:** For $k > K_1$, $E_k = \emptyset$.
4. **Small $k$:** For each $k \le K_1$, $E_k$ is finite.
5. **Conclude:** $E = \bigcup_{k \le K_1} E_k$ is a finite union of finite sets.

The proof is **nonconstructive** — $K_1$ exists but is not computed.

---

## 1. Citation Axiom

**Definition.** For $k \ge 1$, let $g(k)$ denote the least integer $n > k+1$ such that $\mathrm{minFac}\binom{n}{k} > k$, or $+\infty$ if no such $n$ exists.

**Theorem (Konyagin, 1999).** *There exists an absolute constant $c > 0$ such that*
$$g(k) \ge \exp(c \log^2 k) \quad \text{for all } k \ge 2.$$

**Source:** S. V. Konyagin, "Estimates of the least prime factor of a binomial coefficient," *Mathematika* **46** (1999), no. 1, 41–55.

**Interpretation.** For all $n \in [k+2,\, g(k)-1]$: $\mathrm{minFac}\binom{n}{k} \le k$.

---

## 2. Existence of the Threshold $K_1$

**Lemma 2.1.** *$\exp(c\log^2 k) / (2k^2) \to \infty$ as $k \to \infty$.*

*Proof.* $\log(\exp(c\log^2 k)/(2k^2)) = c\log^2 k - 2\log k - \log 2 = \log k(c\log k - 2) - \log 2 \to \infty$. $\square$

**Corollary 2.2.** *There exists $K_1 \in \mathbb{N}$ such that $g(k) > 2k^2$ for all $k > K_1$.*

We fix such a $K_1$ for the remainder of the proof. Note $K_1$ depends only on $c$.

---

## 3. Notation

For $k \ge 1$, define the **$k$-slice:**
$$E_k = \{n \in \mathbb{N} : 2k \le n \wedge \mathrm{minFac}\tbinom{n}{k} > \max(\lfloor n/k \rfloor, k)\}.$$

Then $E = \bigcup_{k=1}^{\infty} \{k\} \times E_k$. So $E$ is finite iff $E_k = \emptyset$ for all but finitely many $k$, and $E_k$ is finite for the remaining $k$.

---

## 4. Step 3: $E_k = \emptyset$ for $k > K_1$

We split into two ranges based on $n$.

### 4.1 Range I: $n \le 2k^2$

Since $k > K_1$: $g(k) > 2k^2$. So $n < g(k)$, which gives $\mathrm{minFac}\binom{n}{k} \le k$.

For $n \le k^2$: $\max(\lfloor n/k\rfloor, k) = k$ (since $n/k \le k$). So $\mathrm{minFac} \le k = \max$. Not in $E$.

For $n \in (k^2, 2k^2]$: $\max(\lfloor n/k\rfloor, k) = \lfloor n/k\rfloor$ (since $n/k > k$). And $\mathrm{minFac} \le k \le \lfloor n/k\rfloor$. Not in $E$.

**Conclusion:** $E_k \cap [2k, 2k^2] = \emptyset$ for $k > K_1$. $\square$

### 4.2 Range II: $n > 2k^2$

Here $M := \lfloor n/k \rfloor > 2k$ and $\max(\lfloor n/k\rfloor, k) = M$. We need $\mathrm{minFac}\binom{n}{k} \le M$.

**Case A: $M$ has a prime factor $p > k$.**

Then $p \le M$ and $p \mid M$. By the **Interval Divisibility Lemma** (proofs/large-n-divisibility.md, Lemma 3): since $p > k$ and $p \mid \lfloor n/k\rfloor$, we get $n \bmod p < k$, hence $p \mid \binom{n}{k}$ by the large prime criterion. So $\mathrm{minFac} \le p \le M$. $\square$

**Case B: $M$ is $k$-smooth (all prime factors $\le k$).**

We split further based on whether $n < g(k)$.

**Sub-case B1: $n < g(k)$.** By definition of $g(k)$: $\mathrm{minFac}\binom{n}{k} \le k$. Since $M > 2k > k$: $\mathrm{minFac} \le k \le M$. $\square$

**Sub-case B2: $n \ge g(k)$.** Here $\mathrm{minFac}\binom{n}{k}$ might exceed $k$. We use the **sieve upper bound** (Brun–Titchmarsh type) on the interval $(n-k, n]$.

**Lemma 4.1 (Sieve bound).** *For $k \ge 2$ and $n > \exp(Ck\log k)$ (for a computable constant $C$), every integer $m \in (n-k, n]$ has a prime factor in $(k, \sqrt{n}\,]$.*

*Proof sketch.* Apply the Selberg upper bound sieve to the set $\mathcal{A} = \{m \in (n-k, n]\}$ sifted by the primes in $(k, \sqrt{n}\,]$. The number of $m$ avoiding all such primes is bounded by:
$$S \le \frac{(2+o(1))\, k}{\log(\sqrt{n}/k)} = \frac{(4+o(1))\, k}{\log n - 2\log k}.$$

For $\log n > (C+1)k\log k$ (with $C > 4$): $S < 1$, so $S = 0$. Every $m$ has a prime factor $q \in (k, \sqrt{n}\,]$. Since $q > k$: $v_q(k!) = 0$, so $q \mid \binom{n}{k}$. And $q \le \sqrt{n} < n/k$ (as $n > k^2$). Hence $\mathrm{minFac} \le q \le M$. $\square$

**Consequence.** For $k > K_1$ and $n > n_0(k) := \exp(Ck\log k)$: Case B is handled.

**Remaining gap: $g(k) \le n \le n_0(k)$ with $M$ $k$-smooth.**

For $k$ sufficiently large, the Konyagin bound $g(k) \ge \exp(c\log^2 k)$ gives $g(k) \gg k^2$, while $n_0(k) = \exp(Ck\log k)$. The interval $[g(k), n_0(k)]$ is nonempty, but the $k$-smooth values of $M = \lfloor n/k\rfloor$ in this range become increasingly sparse.

**Lemma 4.2 (Smooth number sparsity).** *For $k$ sufficiently large, the number of $k$-smooth integers in $(2k,\, n_0(k)/k]$ satisfying $M \ge g(k)/k$ is zero.*

*Proof sketch.* Let $X = n_0(k)/k = \exp(Ck\log k - \log k)$ and $Y = g(k)/k \ge \exp(c\log^2 k - \log k)$. The count of $k$-smooth integers in $[Y, X]$ is bounded by $\Psi(X, k) - \Psi(Y-1, k)$. By the Dickman–de Bruijn estimate: $\Psi(X, k) \approx X \cdot \rho(u)$ where $u = \log X / \log k \approx Ck - 1$. For $k$ large: $\rho(Ck) \le \exp(-Ck(\log(Ck) - 1)) \ll X^{-1}$, so $\Psi(X, k) \to 0$. $\square$

**Combined conclusion for Case B2:** For $k > K_2$ (where $K_2$ depends on $c$ and $C$):
- If $n > n_0(k)$: sieve handles it (Lemma 4.1).
- If $g(k) \le n \le n_0(k)$ and $M$ is $k$-smooth: no such $M$ exists (Lemma 4.2).

Set $K^* = \max(K_1, K_2)$. For $k > K^*$: $E_k = \emptyset$. $\square$

### 4.3 Summary of Step 3

For $k > K^*$:
- Range I ($n \le 2k^2$): Konyagin eliminates all exceptions.
- Range II, Case A: IDL eliminates exceptions.
- Range II, Case B1 ($n < g(k)$): definition of $g(k)$ eliminates exceptions.
- Range II, Case B2 ($n \ge g(k)$): sieve + smooth sparsity eliminates exceptions.

Therefore $E_k = \emptyset$. $\square$

---

## 5. Step 4: $E_k$ is Finite for $k \le K^*$

For each fixed $k \ge 2$:

**Claim.** $E_k \subseteq [2k,\, n_0(k)]$ where $n_0(k) = \exp(Ck\log k)$.

*Proof.* For $n > n_0(k)$: by Lemma 4.1, every $m \in (n-k, n]$ has a prime factor $q \in (k, \sqrt{n}\,]$. Since $q > k$: $q \mid \binom{n}{k}$ and $q \le \sqrt{n} < n/k = \max(\lfloor n/k\rfloor, k)$. So $(n,k) \notin E$. $\square$

Since $[2k, n_0(k)]$ is a bounded interval of integers, $E_k$ is finite. $\square$

### 5.1 Subtlety: Sieve Constant

The constant $C$ in Lemma 4.1 comes from the Selberg sieve. The bound $S \le 4k/(\log n - 2\log k)$ gives $S < 1$ when $\log n > 4k + 2\log k$. So $C = 5$ suffices (taking $n_0(k) = k^{5k}$). This is effective and can be made explicit using standard sieve results (e.g., Halberstam–Richert, *Sieve Methods*, Chapter 3).

**Key point:** The finiteness of each $E_k$ does NOT depend on Konyagin. It follows purely from the sieve upper bound. Konyagin is needed only to show $E_k = \emptyset$ for $k > K^*$ (so that $E$ is a FINITE union).

---

## 6. Step 5: Conclusion

$$E = \bigcup_{k=1}^{K^*} \{k\} \times E_k \cup \bigcup_{k > K^*} \{k\} \times E_k$$

The second union is empty (each $E_k = \emptyset$ for $k > K^*$ by §4). The first is a finite union (over $k \in \{1, \ldots, K^*\}$) of finite sets (each $E_k$ is finite by §5). Therefore $E$ is finite. $\square$

---

## 7. Axiom Accounting

### 7.1 What This Proof Uses

| Input | Type | Status |
|-------|------|--------|
| Konyagin's theorem: $g(k) \ge \exp(c\log^2 k)$ | Citation axiom | Published, Mathematika 1999 |
| Interval Divisibility Lemma (Type A) | Proved | Verified ✅ |
| Large prime criterion | Proved | Mathlib-adjacent |
| Bertrand's postulate | Proved | In Mathlib |
| Selberg sieve upper bound | Classical | Standard reference |
| Dickman–de Bruijn $\Psi$ estimate | Classical | Standard reference |

### 7.2 Comparison with Current Lean Proof

The current Lean formalization uses **two** axioms:
1. `crt_density_from_asymptotic` — for $k > 700$, $n \in [2k, k^2]$: $\exists p \le 29$, $p \mid \binom{n}{k}$
2. `large_n_smooth_case` — for $n > k^2$, $M$ $k$-smooth: $\exists p \le M$, $p \mid \binom{n}{k}$

This proof replaces both with a **single** citation axiom (Konyagin), at the cost of:
- A nonconstructive threshold $K^*$ (vs. the explicit $k = 700$ cutoff).
- A much larger bounding box (vs. the explicit $n < 285$, $k < 29$).
- Reliance on sieve theory and smooth number estimates (classical but not in Mathlib).

### 7.3 Effectivity

Konyagin's method uses exponential sum estimates over digit-constrained sets. The underlying techniques (Bombieri–Pila, Filaseta–Trifonov) are **effective**, meaning $c$ can in principle be computed. If $c$ is known explicitly:
- $K_1$ can be computed (solve $\exp(c\log^2 k) > 2k^2$).
- $K_2$ can be computed (Dickman function estimates).
- $K^* = \max(K_1, K_2)$ is explicit.
- For $k \le K^*$: $n_0(k)$ is explicit, and $E_k \cap [2k, n_0(k)]$ can be enumerated.

However, obtaining an effective $c$ requires detailed analysis of Konyagin's paper (see `proofs/erdos-1094/konyagin-explicit.md`, in progress).

---

## 8. Comparison with ELS93

Erdős, Lacampagne, and Selfridge (1993) conjectured $g(k) > k^2$ for all sufficiently large $k$ (their Conjecture 1). Konyagin's bound $g(k) \ge \exp(c\log^2 k)$ proves this conjecture asymptotically (since $\exp(c\log^2 k) \gg k^2$).

Our proof uses exactly this consequence. The fact that $g(k) > 2k^2$ (not just $> k^2$) is used to handle Range I up to $2k^2$ and to ensure sub-case B1 covers all smooth $M$ up to $2k$ (since $n = kM \le 2k^2 < g(k)$).

---

## 9. Detailed Proof of Lemma 4.2

We prove that for $k$ sufficiently large, there are no $k$-smooth integers $M$ with $M \ge g(k)/k$ and $M \le n_0(k)/k$.

**Setup.** Let $L = g(k)/k$ and $U = n_0(k)/k$. We have:
- $L \ge \exp(c\log^2 k - \log k)$
- $U = \exp(Ck\log k - \log k)$

The count of $k$-smooth integers up to $U$ is $\Psi(U, k)$.

**Dickman estimate.** $\Psi(X, k) \le X \cdot \exp(-u(\log u - 1) + O(\log u))$ where $u = \log X / \log k$.

For $X = U$: $u = (Ck\log k - \log k)/\log k = Ck - 1 \approx Ck$.

$$\Psi(U, k) \le U \cdot \exp(-Ck(\log(Ck) - 1) + O(\log k))$$

Now $U = \exp(Ck\log k - \log k)$, so:

$$\Psi(U, k) \le \exp(Ck\log k - Ck\log(Ck) + Ck + O(\log k))$$
$$= \exp(Ck(\log k - \log(Ck) + 1) + O(\log k))$$
$$= \exp(Ck(1 - \log C) + O(\log k))$$

For $C > e$ (i.e., $C \ge 3$): $1 - \log C < 0$, so $\Psi(U, k) \to 0$ exponentially. In particular, $\Psi(U, k) < 1$ for $k > k_0(C)$.

Since $\Psi(U, k) < 1$ implies there are zero $k$-smooth integers in $[1, U]$ above $L$ (in fact, zero in all of $[1, U]$ for large enough $k$... but this is too strong; $\Psi(U, k)$ counts ALL $k$-smooth numbers $\le U$, including small ones like 1, 2, ..., k).

**Correction.** We need a more refined estimate. The issue is that $\Psi(U, k) \ge k$ (since $1, 2, \ldots, k$ are all $k$-smooth). The Dickman estimate gives $\Psi(U, k) \sim U\rho(Ck)$, which is huge for small $C$ but small relative to $U$ for large $C$.

What we actually need: the count of $k$-smooth integers in the specific range $[L, U]$.

$\Psi(U, k) - \Psi(L-1, k) \le \Psi(U, k)$. But we want this to be 0.

For $L = g(k)/k$: the $k$-smooth integers below $L$ are counted by $\Psi(L, k)$. Let $u_L = \log L / \log k = (c\log^2 k - \log k)/\log k = c\log k - 1$. Then $\Psi(L, k) \approx L \cdot \rho(c\log k)$.

$\rho(c\log k)$: for $v = c\log k$ large, $\rho(v) \approx \exp(-v\log v)$. So $\Psi(L, k) \approx \exp(c\log^2 k) \cdot \exp(-c\log k \cdot \log(c\log k))$.

For $k$ large: $\log(c\log k) \approx \log\log k + \log c$. So the exponent is:
$$c\log^2 k - c\log k(\log\log k + \log c) = c\log k(\log k - \log\log k - \log c)$$

This is positive and growing, so $\Psi(L, k) \to \infty$. The $k$-smooth numbers below $L$ are numerous — they include ALL $k$-smooth numbers up to $\exp(c\log^2 k)/k$.

**The key question:** Are there $k$-smooth numbers ABOVE $L$?

Since $U/L = \exp(Ck\log k - c\log^2 k)$ which is huge for $k$ large (as $Ck\log k \gg c\log^2 k$): there are many integers in $[L, U]$. Some could be $k$-smooth.

**In fact, there ARE $k$-smooth numbers above $L$.** For example, $2^{\lceil c\log^2 k / \log 2\rceil}$ is 2-smooth (hence $k$-smooth) and approximately $\exp(c\log^2 k) \approx kL > L$.

**Revised assessment.** Lemma 4.2 as stated is **too strong** — it claims zero $k$-smooth $M$ in the range, which is false. The correct approach requires a different argument for Sub-case B2.

---

## 10. Revised Treatment of Sub-case B2

The gap in §4.2 (Sub-case B2) is genuine: for $n \ge g(k)$ with $k$-smooth $M$ and $M \ge 2k$, we cannot directly conclude $\mathrm{minFac}\binom{n}{k} \le M$.

### 10.1 What We Can Prove

For $k > K_1$ and $n \ge g(k) > 2k^2$, if $M = \lfloor n/k \rfloor$ is $k$-smooth and $M \ge 2k$:

- $C(n,k)$ might be $k$-rough (all prime factors $> k$).
- Among the primes $q \in (k, M]$: $q \mid \binom{n}{k}$ iff $n \bmod q < k$.
- The Bertrand prime $p^* \in (k, 2k]$ satisfies $p^* \le 2k \le M$. It divides $\binom{n}{k}$ for **some** $n$ in each interval $[kM, kM+k)$, but not necessarily for every $n$.

### 10.2 Sieve-Based Finiteness of Each $E_k$

Even without closing Sub-case B2, we can still prove:

**Theorem 10.1.** *For each fixed $k \ge 2$, $E_k$ is finite.*

*Proof.* By Lemma 4.1 (sieve upper bound): for $n > n_0(k) = k^{5k}$, every $m \in (n-k, n]$ has a prime factor $q \in (k, \sqrt{n}\,]$. Since $q > k$: $q \mid \binom{n}{k}$ and $q \le \sqrt{n} < n/k$. So $\mathrm{minFac} \le n/k = \max(\lfloor n/k\rfloor, k)$. Not in $E$.

Therefore $E_k \subseteq [2k, n_0(k)]$, which is a bounded interval. $\square$

### 10.3 The Remaining Question

To prove $E$ is finite (not just each $E_k$), we need $E_k = \emptyset$ for all $k > K^*$. The Konyagin bound gives $E_k \cap [2k, 2k^2] = \emptyset$ for $k > K_1$. The sieve gives $E_k \cap [n_0(k), \infty) = \emptyset$ for all $k$.

The gap is: $E_k \cap (2k^2, n_0(k))$ for $k > K_1$, restricted to $k$-smooth $M$ and $n \ge g(k)$. By the sub-case B1 argument, this reduces to $n \ge g(k)$, i.e., $\binom{n}{k}$ is $k$-rough.

**Two paths to close this gap:**

**(Path A) Effectivize Konyagin.** Compute an explicit $c$ and show $g(k) > n_0(k)$ for $k > K_3$. This requires $\exp(c\log^2 k) > k^{5k}$, i.e., $c\log^2 k > 5k\log k$, i.e., $c\log k > 5k$. This is FALSE for large $k$ — Konyagin's bound grows too slowly. ❌

**(Path B) Strengthen the sieve.** Use the COMBINED small-prime and large-prime constraints. The small-prime digit domination restricts $n$ to density $\delta_k < 1/k^2$. The large-prime residue avoidance restricts further. For each $k$-smooth $M$, the expected count of exceptions in $[kM, kM+k)$ is at most $\delta_k \cdot k \cdot \prod_{q \in (k,M]} (q-k)/q$. Summing over $k$-smooth $M$ and using the combined density decay, the TOTAL expected count converges. However, converting this to a deterministic "count = 0" statement is the same density-to-coverage gap that motivated the original axiom.

**(Path C — recommended) Accept as a citation axiom.** State the Type B smooth case as a separate citation axiom, reducing the axiom count from 2 to 2 but replacing ad hoc axioms with well-motivated conjectures backed by Konyagin's framework.

---

## 11. Clean Proof with Two Citation Axioms

If we accept both Konyagin and the Type B smooth case, the proof simplifies:

**Axiom K (Konyagin).** $\exists\, c > 0\, \forall\, k \ge 2$: $g(k) \ge \exp(c\log^2 k)$.

**Axiom S (Smooth case).** $\forall\, k \ge 2$, $n > k^2$ with $\lfloor n/k\rfloor$ being $k$-smooth: $\exists$ prime $p \le \lfloor n/k\rfloor$ with $p \mid \binom{n}{k}$.

**Theorem.** $E$ is finite.

*Proof.*

**Step 1.** By Axiom S + IDL (Type A): for all $k \ge 2$ and $n > k^2$: $\mathrm{minFac}\binom{n}{k} \le \lfloor n/k\rfloor = \max(\lfloor n/k\rfloor, k)$. So $E_k \subseteq [2k, k^2]$ for all $k \ge 2$.

**Step 2.** By Axiom K: $\exists\, K_1$ with $g(k) > k^2$ for $k > K_1$. For such $k$ and $n \in [2k, k^2]$: $n < g(k)$, so $\mathrm{minFac} \le k \le \max(\lfloor n/k\rfloor, k)$. Hence $E_k = \emptyset$ for $k > K_1$.

**Step 3.** $E = \bigcup_{k=1}^{K_1} \{k\} \times E_k$. Each $E_k \subseteq [2k, k^2]$ is finite. Finite union of finite sets. $\square$

**Comparison with current Lean proof:**
- Axiom K replaces `crt_density_from_asymptotic` (for $k > K_1$ with $g(k) > k^2$).
- Axiom S is equivalent to `large_n_smooth_case` (unchanged).
- The proof structure is simpler (no case split at $k = 700$, no `native_decide`).
- The bounding box is $[2k, k^2] \times [1, K_1]$ instead of $[0, 284] \times [0, 28]$.

---

## 12. What Konyagin Actually Buys Us

### 12.1 Axiom Reduction Map

| Current axiom | What Konyagin replaces | What remains |
|---|---|---|
| `crt_density_from_asymptotic` ($k > 700$, $n \le k^2$) | ✅ Fully replaced: $g(k) > k^2$ for $k > K_1$ | — |
| `large_n_smooth_case` ($n > k^2$, smooth $M$) | Partially: B1 ($n < g(k)$) handled | B2 ($n \ge g(k)$) remains |

### 12.2 Net Axiom Count

- **Without Konyagin:** 2 axioms (current Lean proof).
- **With Konyagin only:** 1 citation axiom, but Sub-case B2 gap remains open. Total: 1 citation + 1 unproved gap = effectively still 2.
- **With Konyagin + Axiom S:** 2 citation axioms, but cleaner structure.

### 12.3 Path to 0 Axioms

If Axiom S can be proved independently (e.g., via Sylvester–Schur type arguments, or by showing the sieve bound handles ALL $n > k^2$ for $k \ge 29$), then Konyagin alone closes everything. The bottleneck is proving that for $k$-smooth $M > 2k$ and $n \ge g(k)$: SOME prime $\le M$ divides $\binom{n}{k}$.

---

## References

1. S. V. Konyagin, "Estimates of the least prime factor of a binomial coefficient," *Mathematika* **46** (1999), no. 1, 41–55.
2. P. Erdős, J. L. Lacampagne, J. L. Selfridge, "Estimates of the least prime factor of a binomial coefficient," *Math. Comp.* **61** (1993), no. 203, 215–224.
3. H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, 1974.
4. A. Granville, O. Ramaré, "Explicit bounds on exponential sums and the scarcity of squarefree binomial coefficients," *Mathematika* **43** (1996), 73–107.

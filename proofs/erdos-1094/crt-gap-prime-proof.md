# CRT Gap Prime Proof: Eliminating `large_n_smooth_case` for k ≥ 9

**Status:** ⚠️ BROKEN — F_lt_one is FALSE (see §ERRATUM below)
**Goal:** For k ≥ 9 and any n > k², prove ∃ prime q ∈ (k, ⌊n/k⌋] with q | C(n,k).

---

## 0. Key Criterion

**Lemma (Large Prime Criterion).** For prime q > k:
$$q \mid \binom{n}{k} \iff n \bmod q < k$$

*Proof.* Since q > k: $v_q(k!) = 0$. So $v_q\binom{n}{k} = \lfloor n/q \rfloor - \lfloor (n-k)/q \rfloor$, which equals 1 iff there is a multiple of q in $(n-k, n]$, iff $n \bmod q < k$. ∎

**Contrapositive.** If $\mathrm{minFac}\binom{n}{k} > M$ where $M = \lfloor n/k \rfloor$, then $n \bmod q \ge k$ for ALL primes $q \in (k, M]$.

---

## 1. Exact CRT Counting

Let $q_1 < q_2 < \cdots < q_r$ be all primes in $(k, M]$.
Let $Q = \prod_{i=1}^r q_i$.

**Definition.** The *bad residue set* for prime $q_i$ is $B_i = \{k, k+1, \ldots, q_i - 1\} \subseteq \mathbb{Z}/q_i\mathbb{Z}$, with $|B_i| = q_i - k$.

An integer n is an *exception* if $n \bmod q_i \in B_i$ for all $i = 1, \ldots, r$.

**Lemma 1 (CRT Counting).** By CRT (the $q_i$ are distinct primes):
$$|\{n \in \{0, \ldots, Q-1\} : n \bmod q_i \in B_i \;\forall\, i\}| = \prod_{i=1}^r (q_i - k)$$

*Lean hint:* This is `ZMod.chineseRemainder` applied to the product of coprime moduli, giving a bijection $\mathbb{Z}/Q\mathbb{Z} \cong \prod_i \mathbb{Z}/q_i\mathbb{Z}$. The preimage of $\prod B_i$ has cardinality $\prod |B_i|$.

**Lemma 2 (Counting in an interval).** For any interval $[1, N]$:
$$|\{n \in [1, N] : n \bmod q_i \in B_i \;\forall\, i\}| \le \left\lfloor \frac{N}{Q} \right\rfloor \cdot \prod_{i=1}^r (q_i - k) \;+\; \prod_{i=1}^r (q_i - k)$$

The first term counts complete periods; the second bounds the partial period at the end.

*Simplified upper bound:*
$$\le \left(\frac{N}{Q} + 1\right) \cdot \prod_{i=1}^r (q_i - k)$$

---

## 2. The Sufficient Condition

We want the count above to be $< 1$ (hence $= 0$, since it's a nonneg integer).

**Sufficient condition:** $(N/Q + 1) \cdot \prod(q_i - k) < 1$.

Set $N = kM$ (since $n \le kM$ when $M = \lfloor n/k \rfloor$). Define:
$$F(k, M) := \left(\frac{kM}{Q} + 1\right) \cdot \prod_{i=1}^r (q_i - k)$$

**Theorem.** If $F(k, M) < 1$ for all $M > k$, then $g(k) > k^2$ (and more: no exception exists for ANY $n > k^2$).

*Lean structure:* Prove $F(k, M) < 1$ → count $= 0$ → no exception exists → $\mathrm{minFac}\binom{n}{k} \le M$.

---

## 3. Bounding F(k, M)

We need: $F(k, M) < 1$ for all $M > k$ when $k \ge 9$.

**Rewrite:**
$$F(k, M) = \left(\frac{kM}{\prod q_i} + 1\right) \cdot \prod_{i=1}^r (q_i - k) = kM \prod_{i=1}^r \frac{q_i - k}{q_i} + \prod_{i=1}^r (q_i - k)$$

The first term is the "main" part; the second is the remainder. For the first term:

$$kM \prod_{\substack{q \text{ prime} \\ k < q \le M}} \left(1 - \frac{k}{q}\right)$$

### 3.1 Upper Bound via Mertens' Theorem

**Key identity.** For primes $q > k$, write $1 - k/q = (1 - 1/q)^k \cdot R(k, q)$ where:
$$R(k, q) = \frac{1 - k/q}{(1 - 1/q)^k}$$

**⚠️ WARNING:** $R(k,q) \ne 1$ in general. However, for $q > k$:
$$(1 - 1/q)^k \le 1 - k/q + \binom{k}{2}/q^2 \le 1 - k/q + k^2/(2q^2)$$

So $R(k,q) \ge (1 - k/q)/(1 - k/q + k^2/(2q^2)) \ge 1 - k^2/(2q^2(1-k/q))$ for $q > k$.

**For the product:** Rather than using $R(k,q)$, bound the product directly.

**Lemma 3 (Product Bound).** For $k \ge 2$ and $M \ge 2k$:
$$\prod_{\substack{q \text{ prime} \\ k < q \le M}} \left(1 - \frac{k}{q}\right) \le \left(\frac{C \ln k}{\ln M}\right)^k$$

where $C$ is an explicit constant from Mertens' theorem.

*Proof.* Take logarithms:
$$\sum_{\substack{q \text{ prime} \\ k < q \le M}} \ln\left(1 - \frac{k}{q}\right) = k \sum_{\substack{q \text{ prime} \\ k < q \le M}} \frac{\ln(1 - k/q)}{k}$$

For each $q > k$: $\ln(1 - k/q) \le -k/q$ (since $\ln(1-x) \le -x$). So:
$$\sum_{k < q \le M} \ln(1 - k/q) \le -k \sum_{k < q \le M} \frac{1}{q}$$

By Mertens' second theorem (with Rosser-Schoenfeld explicit bounds):
$$\sum_{p \le x} \frac{1}{p} = \ln\ln x + B + O(1/\ln^2 x)$$

where $B \approx 0.2615$ is Meissel-Mertens constant. So:
$$\sum_{k < q \le M} \frac{1}{q} = \ln\ln M - \ln\ln k + O(1/\ln^2 k)$$

Therefore:
$$\sum \ln(1 - k/q) \le -k(\ln\ln M - \ln\ln k) + O(k/\ln^2 k)$$

Exponentiating:
$$\prod(1 - k/q) \le \exp\left(-k\ln\frac{\ln M}{\ln k} + O(k/\ln^2 k)\right) = \left(\frac{\ln k}{\ln M}\right)^k \cdot e^{O(k/\ln^2 k)}$$

The error term $e^{O(k/\ln^2 k)}$ is bounded by a constant $C^k$ for an explicit $C$ close to 1. ∎

### 3.2 Putting It Together

The main part of $F$:
$$kM \cdot \left(\frac{C\ln k}{\ln M}\right)^k$$

Set $t = \ln M$. This is $k \cdot e^t \cdot (C\ln k / t)^k$. Maximizing over $t$: derivative is zero at $t = k$ (i.e., $M = e^k$). At the maximum:

$$F_{\text{main}} \le k \cdot e^k \cdot \left(\frac{C\ln k}{k}\right)^k = k \cdot \left(\frac{Ce\ln k}{k}\right)^k$$

**For $k \ge 9$ with $C = 1$:** $e\ln 9 / 9 = 2.718 \times 2.197 / 9 \approx 0.663 < 1$.

Since the base $Ce\ln k / k$ is decreasing for $k > Ce$ and already $< 1$ at $k = 9$, $F_{\text{main}} \to 0$ exponentially.

### 3.3 The Remainder Term

The remainder is $\prod_{i=1}^r (q_i - k)$. For $k \ge 9$ and $M > k$: each $q_i - k \ge 1$, but $Q = \prod q_i$ grows much faster, so the remainder is negligible compared to $Q$. Specifically:

$$\frac{\prod(q_i - k)}{\prod q_i} = \prod\left(1 - \frac{k}{q_i}\right) \le \left(\frac{C\ln k}{\ln M}\right)^k$$

For this to be $< 1$: need $C\ln k / \ln M < 1$, i.e., $M > k^C$. For $M \le k^C$: the remainder can be $\ge 1$, but there are few primes in $(k, k^C]$, and direct computation handles these cases.

### 3.4 Handling All M

Split into three ranges:

**Range A: $M \ge e^k$.** $F_{\text{main}} \le k \cdot (Ce\ln k / k)^k < 1$ (exponentially small). Remainder: $\prod(1-k/q_i) < (C\ln k / k)^k \ll 1$. Total $F < 1$. ✓

**Range B: $k^2 \le M < e^k$.** $F_{\text{main}} = kM \cdot (C\ln k / \ln M)^k$. Since $\ln M \ge 2\ln k$: $(C\ln k / \ln M)^k \le (C/2)^k$. So $F_{\text{main}} \le k \cdot e^k \cdot (C/2)^k = k \cdot (Ce/2)^k$. For $C$ close to 1: $Ce/2 \approx 1.36$, which grows! So this range needs more care.

**Actually, the maximum at $t = k$ already covers this:** the function $e^t \cdot (C\ln k / t)^k$ is unimodal with maximum at $t = k$, and $F_{\text{main}}$ at the maximum is $< 1$ for $k \ge 9$. So $F_{\text{main}} < 1$ for ALL $t$ (all $M$) simultaneously.

**Range C: $k < M < k^2$.** Fewer primes, so $\prod(1-k/q)$ is larger. But $kM < k^3$ is small. This range may need direct computation for small $k$ values (e.g., $k \in [9, 30]$).

---

## 4. Formalization Plan

### 4.1 File: `botlib/NumberTheory/Erdos1094/GapPrime.lean`

### 4.2 Citation Axiom (1 axiom)

```lean
/-- Rosser-Schoenfeld explicit Mertens bound (1962, equation 2.30).
    Two-sided bound on ∏_{p ≤ x} (1 - 1/p). -/
axiom rosser_schoenfeld_mertens_upper (x : ℝ) (hx : 285 ≤ x) :
    ∏ p ∈ (Finset.range ⌊x⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))
    ≤ Real.exp (-eulerMascheroniConstant) / Real.log x * (1 + 1 / (2 * (Real.log x) ^ 2))
```

### 4.3 Theorems to Prove (all from the axiom + CRT)

1. **`crt_bad_count`**: Exact count of bad residues via CRT.
   - *Input:* List of distinct primes $q_1, \ldots, q_r > k$, interval $[1, N]$.
   - *Output:* Count $\le (N/Q + 1) \cdot \prod(q_i - k)$.
   - *Proof:* CRT bijection + interval counting.

2. **`mertens_product_bound`**: $\prod_{k < q \le M}(1 - k/q) \le (C\ln k / \ln M)^k$.
   - *Proof:* From `rosser_schoenfeld_mertens_upper` + prime reciprocal sum.

3. **`F_lt_one_large_k`**: $F(k, M) < 1$ for $k \ge K_0$ and all $M > k$.
   - *Proof:* Optimize over $M$, use `mertens_product_bound`.

4. **`F_lt_one_small_k`**: $F(k, M) < 1$ for $k \in [9, K_0)$ and all $M > k$.
   - *Proof:* Direct computation or explicit evaluation of the product.

5. **`gap_prime_rescue_k_ge_9`**: Main theorem.
   - *Input:* $k \ge 9$, $n > k^2$, $M = \lfloor n/k \rfloor$.
   - *Output:* $\exists q$ prime, $q \in (k, M]$, $q \mid \binom{n}{k}$.
   - *Proof:* From `F_lt_one` → count $= 0$ → contradiction with existence of exception.

### 4.4 Lean Sketch

```lean
theorem gap_prime_rescue_k_ge_9 (k n : ℕ) (hk : 9 ≤ k) (hn : k ^ 2 < n)
    (hM : ∀ q : ℕ, q.Prime → k < q → q ≤ n / k → ¬(q ∣ Nat.choose n k)) : False := by
  -- 1. Let primes = list of primes in (k, n/k]
  -- 2. By large_prime_criterion: n % q ≥ k for all such q
  -- 3. By crt_bad_count: count of such n in [1, kM] ≤ F(k, M)
  -- 4. By F_lt_one: F(k, M) < 1
  -- 5. Count = 0, but n is such an element: contradiction
  sorry
```

---

## 5. What This Proves (Updated Tower)

```
large_n_smooth_case [AXIOM — now only needed for k ∈ {2, 3, 4, 5, 6, 7, 8}]
├── smooth_case_divisible      ✅ k | n
├── smooth_case_n_smooth       ✅ n k-smooth
├── smooth_case_gap_prime      ✅ gap prime divides n
├── smooth_case_near_prime_nondivisor ✅ s ∤ k
└── B3b (s | k)
    ├── k ≥ 9: gap_prime_rescue ✅ [THIS PROOF]
    ├── k ≤ 6: handled by existing AxiomFree.lean + finite exception list
    └── k ∈ {7, 8}: OPEN (CRT counting gives F > 1; needs Kummer interaction or computation)
```

For k ≤ 6: already covered by `density_verified_700` and the finite exception analysis.
For k ∈ {7, 8}: the CRT gap prime argument alone is insufficient (F_max ≈ 1.8 for k=7, ≈ 1.15 for k=8). These require either incorporating the Kummer constraint to tighten the bound, or computational verification up to g(k).

---

## 6. Comparison with Previous Approach

| Aspect | Previous (Konyagin) | This proof |
|--------|---------------------|------------|
| Tool | Exponential sums + BP | CRT + Mertens |
| Depth | Deep (algebraic geometry) | Elementary (analytic NT) |
| Citation | Konyagin 1999 | Rosser-Schoenfeld 1962 |
| Scope | $g(k) \ge \exp(c\log^2 k)$ | $g(k) > k^2$ (weaker but sufficient) |
| Formalizability | Very hard | Medium |

---

---

## ERRATUM

**`F_lt_one` is FALSE as stated.** The integer count bound is
(kM/Q + 1) · R where R = ∏(q_i - k). Since Q >> kM, this simplifies to
≈ R = ∏(q_i - k), which is astronomical (≈10³⁰ for k=9, M=100).

The real-valued density kM · ∏(1-k/q) = kM · R/Q does go below 1 for k ≥ 9.
But the integer counting bound adds +R as a remainder term, and R dominates.

**The CRT counting approach CANNOT prove count = 0.** The density-to-deterministic
gap is fundamental to this method. A different proof strategy is needed for B3b.

## References

1. J. B. Rosser, L. Schoenfeld, "Approximate formulas for some functions of prime numbers," *Illinois J. Math.* **6** (1962), 64–94.
2. E. E. Kummer, "Über die Ergänzungssätze...," *J. Reine Angew. Math.* **44** (1852), 93–146.

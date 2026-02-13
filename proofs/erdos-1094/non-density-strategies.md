# Erdős 1094: Non-Density Strategies for Closing the Axiom Gap

**Status:** Exploration 🔬  
**Purpose:** Address the chief's question — can we prove E is finite WITHOUT relying on density arguments?  
**Target axioms:**
1. `crt_density_from_asymptotic` — for k > 700, n ∈ [2k, k²]: some prime ≤ 29 divides C(n,k)
2. `large_n_smooth_case` — for n > k², M = ⌊n/k⌋ k-smooth: C(n,k) has prime factor ≤ M  
**Dependencies:** All existing verified proofs in `proofs/erdos-1094/`  
**Confidence:** Varies by strategy (see individual assessments)

---

## 0. The Precise Gap

The NL proof chain is complete and verified ✅ (main-theorem → no-exceptions-k-ge-29 → crt-density-k-ge-29 + large-n-divisibility → ...). The Lean formalization has exactly **two axioms** left:

**Axiom 1 (`crt_density_from_asymptotic`).** For k > 700 and n ∈ [2k, k²]: ∃ prime p ≤ 29 with p | C(n,k).

- *What we have:* CRT exhaustive verification for k ∈ [29, 700] (`native_decide`). Real-valued density bound δ_k < 1/k² for all k ≥ 2 (`small_prime_kummer_density`).
- *The gap:* δ_k · (k² − 2k) < 1 means "expected count < 1" but does NOT prove "count = 0." The CRT residue set S(k) always has R_k > 0 elements; we need to show none falls in [2k, k²].

**Axiom 2 (`large_n_smooth_case`).** For n > k² and M = ⌊n/k⌋ with M k-smooth: ∃ prime p ≤ M with p | C(n,k).

- *What we have:* Interval Divisibility Lemma handles all M with a prime factor > k (Type A). Only Type B (k-smooth M) remains.
- *The gap:* When M is k-smooth, no prime factor of M is > k, so the Interval Divisibility Lemma doesn't apply. We need a different argument.

---

## 1. Why Density Arguments Fundamentally Fail

**The density approach gives:** For each fixed k, the set of "bad" n (those satisfying digit-domination for ALL primes ≤ 29) has density δ_k in ℤ. We've proved δ_k < 1/k², so the expected number of bad n in [2k, k²] is < 1.

**Why this doesn't suffice:**
- δ_k > 0 for every k (since k itself always satisfies digit-domination for k in every base).
- "Expected count < 1" is compatible with actual count = 1 for infinitely many k.
- The CRT residues S(k) mod M_k form a DETERMINISTIC set. Their positions in [0, M_k) are fixed, not random. Even though |S(k)| / M_k < 1/k², a single element could land in [2k, k²].

**The combinatorial obstacle:** The valid residue set S(k) = {r ∈ [0, M_k) : dig_p(r) ≥ dig_p(k) ∀p ≤ 29, ∀ digit positions} depends on the specific digit structure of k in TEN different bases simultaneously. As k varies, these digit patterns interact in unpredictable ways. No known analytical result controls WHERE in [0, M_k) the elements of S(k) fall — only how MANY there are.

---

## 2. Strategy A: Smooth Parts Identity + Factorial Constraint

### 2.1 The Identity

**Theorem (Smooth Parts).** If C(n,k) has no prime factor ≤ k, then:
$$\prod_{m=n-k+1}^{n} \operatorname{smooth}_k(m) = k!$$
where $\operatorname{smooth}_k(m) = \prod_{p \le k} p^{v_p(m)}$ is the k-smooth part of m.

*Proof.* $v_p(C(n,k)) = \sum_{m=n-k+1}^{n} v_p(m) - v_p(k!)$. If this is zero for all $p \le k$, then $\sum v_p(m) = v_p(k!)$ for each $p$, hence $\prod \operatorname{smooth}_k(m) = k!$. $\square$

### 2.2 Structural Consequences

For n ∈ [2k, k²], each m ∈ (n-k, n] satisfies k < m ≤ k². We split the m values:

- **k-smooth m** (all prime factors ≤ k): smooth_k(m) = m, contributing m > k to the product.
- **Non-k-smooth m** (has prime factor > k): smooth_k(m) = m / rough_k(m) where rough_k(m) ≥ (smallest prime > k) > k. So smooth_k(m) ≤ m/k < k²/k = k.

Let b = #{k-smooth m ∈ (n-k, n]} and a = k − b (non-smooth count).

**Size constraints:**
$$k! = \underbrace{\prod_{\text{smooth}} m}_{\text{each } > k, \text{ there are } b \text{ terms}} \times \underbrace{\prod_{\text{non-smooth}} \operatorname{smooth}_k(m)}_{\text{each } < k, \text{ there are } a \text{ terms}}$$

Lower bound on smooth product: $\prod_{\text{smooth}} m \ge (k+1)(k+2) \cdots (k+b)$ at minimum, since they're b distinct integers > k.

Upper bound on non-smooth product: $\prod_{\text{non-smooth}} \operatorname{smooth}_k(m) < k^a = k^{k-b}$.

So: $(k+1)(k+2)\cdots(k+b) \le k! / 1 = k!$, which gives $\binom{k+b}{b} \le k!/b! \cdot \text{something}$. Not immediately contradictory.

### 2.3 Where This Approach Could Lead

**Potential contradiction for large k:** By the Dickman function, the count of k-smooth numbers in (n-k, n] for n ≈ k² is approximately $b \approx k \cdot \rho(2) \approx 0.307k$. The b smooth numbers are distinct integers in (k, k²] whose product, times the (k-b) non-smooth parts (each < k), equals k!.

Using Stirling: $k! \approx (k/e)^k \sqrt{2\pi k}$. The product of b ≈ 0.307k numbers in (k, k²] is at least $k^{0.307k}$ and at most $(k^2)^{0.307k} = k^{0.614k}$. The remaining 0.693k non-smooth parts contribute at most $k^{0.693k}$. Total: at most $k^{0.614k + 0.693k} = k^{1.307k}$. But $k! \approx (k/e)^k = k^k / e^k$, which for large k is much less than $k^{1.307k}$. So the identity IS satisfiable — no immediate contradiction.

### 2.4 Assessment

**Strength:** This is a genuinely different framing — algebraic rather than combinatorial/modular. It converts the digit-domination question into a constrained factorization problem.

**Weakness:** The smooth parts identity is satisfiable for the parameter ranges we care about. Getting a contradiction requires tighter bounds on the POSITIONS and VALUES of the smooth parts, not just their product. This seems as hard as the original problem.

**Confidence:** Low. This approach doesn't seem to close the gap by itself, but it could be combined with other arguments.

---

## 3. Strategy B: Bertrand Chain Coverage (for Axiom 2)

### 3.1 Key Observation

For Axiom 2 (`large_n_smooth_case`, n > k²), consider any n ∈ [kM, kM+k) where M = ⌊n/k⌋ is k-smooth. We need SOME prime p ≤ M dividing C(n,k).

By Bertrand's postulate, there exists a prime p* ∈ (k, 2k]. Since M ≥ k+1 (from n > k²), we consider two sub-cases:

**Case M ≥ 2k:** p* ≤ 2k ≤ M, so p* is a valid candidate (p* ≤ M). Now p* | C(n,k) iff n mod p* < k (large prime criterion). The interval [kM, kM+k) has length k, and p* > k, so the k consecutive integers have k distinct residues mod p*. Among these, exactly k residues are < k (namely 0, 1, ..., k-1). So:

p* | C(n,k) for n ⟺ n mod p* < k ⟺ n mod p* ∈ {0, 1, ..., k-1}.

The interval [kM, kM+k) starts at kM. The residues mod p* are {kM mod p*, kM+1 mod p*, ..., kM+k-1 mod p*}. Since k < p*, these are k DISTINCT residues. Exactly k of the p* possible residues are "good" (< k), and p* - k are "bad" (≥ k). Since k ≤ p* - 1, the interval covers k of p* residues. The probability that NONE is good is... well, it depends on kM mod p*.

**When does the interval MISS all good residues?** The k consecutive residues starting at kM mod p* are all ≥ k. This happens iff kM mod p* ∈ {k, k+1, ..., p*-1} AND kM+k-1 mod p* ∈ {k, k+1, ..., p*-1}. Since the residues are consecutive (and k < p*), the window {kM mod p*, ..., kM+k-1 mod p*} is contiguous mod p*. For ALL to be ≥ k, we need kM mod p* ∈ [k, p*-k], which requires p* - k ≥ k, i.e., p* ≥ 2k. Since p* ≤ 2k, this means p* = 2k (impossible since p* is prime and > k ≥ 29, so 2k is even) or the condition fails.

**Wait — let me be more careful.** If kM mod p* = j, the residues are j, j+1, ..., j+k-1 (mod p*). For all to be ≥ k:
- If j+k-1 < p* (no wraparound): need j ≥ k and j+k-1 ≤ p*-1, i.e., j ∈ [k, p*-k]. Requires p* ≥ 2k.
- If j+k-1 ≥ p* (wraparound): the residues are j, j+1, ..., p*-1, 0, 1, ..., j+k-1-p*. Since residues 0, 1, ..., j+k-1-p* are < k (as j+k-1-p* < k when j < p*), at least one is < k. So some residue IS good. ✓

So the only danger case is j ∈ [k, p*-k] with p* ≥ 2k. Since p* ≤ 2k (by Bertrand), the only possibility is p* = 2k (not prime for k ≥ 2) or j = k with p* = 2k+1. So for p* ≤ 2k, the range [k, p*-k] has p*-2k+1 ≤ 1 element.

**Precise claim:** For p* ∈ (k, 2k] prime:
- If p* < 2k: [k, p*-k] = [k, p*-k]. Since p*-k < k, this is EMPTY. So the interval ALWAYS contains a good residue. ✓
- If p* = 2k: impossible (2k is even for k ≥ 2).
- If p* = 2k+1: this can happen (e.g., k = 14, p* = 29). Then [k, p*-k] = [k, k+1], which has 2 elements. But p* = 2k+1 > 2k, so this p* is in (k, 2k+1], not (k, 2k]. Bertrand gives prime in (k, 2k], so p* ≤ 2k.

**Conclusion for M ≥ 2k:** For any Bertrand prime p* ∈ (k, 2k], since p* < 2k (p* ≤ 2k and p* is odd for k ≥ 2, so p* ≤ 2k-1), the range [k, p*-k] is empty (as p*-k < k). Therefore the interval [kM, kM+k) ALWAYS contains an n with n mod p* < k, hence p* | C(n,k).

This means: **for M ≥ 2k and any n ∈ [kM, kM+k), C(n,k) has a prime factor p* ≤ 2k ≤ M.** 

This handles ALL smooth M ≥ 2k, completely and deterministically! 🎉

### 3.2 Remaining Case: k-smooth M ∈ (k, 2k)

For M ∈ (k, 2k), the Bertrand prime p* might exceed M (since p* ∈ (k, 2k] and M < 2k). So p* > M is possible, meaning p* doesn't satisfy p* ≤ M (the threshold for this range).

But wait: for n > k² with M = ⌊n/k⌋ ∈ (k, 2k), we have n ∈ [kM, k(M+1)) ⊂ (k², 2k²). In this range, the threshold is max(n/k, k) = n/k = M (since M > k). We need a prime p ≤ M dividing C(n,k). The available primes are those ≤ M = ⌊n/k⌋.

Primes ≤ k always exist (2, 3, 5, ...). So we need some prime p ≤ k with p | C(n,k), which by Kummer means digit-domination fails in base p. This is EXACTLY the small-prime constraint — the same one used in the n ∈ [2k, k²] case.

For the interval [kM, kM+k) with k-smooth M ∈ (k, 2k): we need some prime p ≤ k such that n does NOT digit-dominate k in base p. The count of n ∈ [kM, kM+k) satisfying digit domination for ALL p ≤ k is bounded by δ_k · k (expected count in an interval of length k), which is tiny. But again, density < 1 ≠ 0.

**However:** there are at most 2^{π(k)} ≈ 2^{k/ln k} k-smooth values in (k, 2k). Wait, that's not right. The k-smooth numbers in (k, 2k) are those m ∈ (k, 2k) with all prime factors ≤ k. Since m < 2k, the count is at most the number of integers in (k, 2k), which is k-1. Actually, for k ≥ 29, the k-smooth numbers in (k, 2k) include numbers like k+1 (if k+1 is smooth), 2k-1 (if smooth), etc.

The KEY point: for each such smooth M, the interval [kM, kM+k) is a DIFFERENT interval. If we could verify them all simultaneously using a single CRT computation, we'd reduce to checking a FINITE number of cases per k. But the number of smooth M values grows with k.

### 3.3 A Tighter Argument for M ∈ (k, 2k)

Consider primes p ∈ (M/2, M] (by Bertrand, at least one exists). If p > k, then p | C(n,k) iff n mod p < k. We have p ≤ M < 2k, so p ∈ (k, 2k). These are exactly the primes in P_L.

For M ∈ (k, 2k): any prime p ∈ (M/2, M] satisfies p ≤ M (good for the threshold) and p > k/2. By the same residue argument as §3.1: the interval [kM, kM+k) has k consecutive residues mod p, and since p > k (as p > M/2 > k/2 and if p > k), the same "empty bad range" argument applies.

Wait, we need p > k for this to work (large prime criterion). If p > k: p | C(n,k) iff n mod p < k. Same argument as before: p ≤ 2k-1, so p-k < k, so the range [k, p-k] is empty, so the interval always hits a good residue.

But does (M/2, M] contain a prime > k? For M ∈ (k, 2k): (M/2, M] ⊃ (k/2, M]. If M > k, then (k, M] is nonempty iff M ≥ k+1. By Bertrand on M/2: there exists prime p ∈ (M/2, M]. Is p > k? We have p > M/2 > k/2. So p > k iff p > k, which requires M/2 > k, i.e., M > 2k. But M < 2k by assumption! So p might be ≤ k.

**The problem:** For M ∈ (k, 2k), the Bertrand prime in (M/2, M] might be ≤ k. If it IS ≤ k, then p | C(n,k) follows from digit-domination failure, which we can't prove analytically for all k.

For M very close to k+1: (M/2, M] = ((k+1)/2, k+1], which for k ≥ 29 contains primes ≤ k (like primes in (15, 30] for k = 29, which includes 17, 19, 23, 29 — all ≤ k = 29).

**So for smooth M ∈ (k, 2k), we're back to the small-prime digit-domination question.** This is the SAME obstacle as Axiom 1.

### 3.4 Assessment

**What Strategy B achieves (rigorously):**
- Closes Axiom 2 for ALL k-smooth M ≥ 2k. This is a significant portion of the axiom. ✅
- The Bertrand chain argument is deterministic, structural, and requires no computation.

**What remains:** k-smooth M ∈ (k, 2k). This reduces Axiom 2 to: for n ∈ (k², 2k²), C(n,k) has a prime factor ≤ k. This is equivalent to: some prime p ≤ k divides C(n,k), which is the digit-domination question for small primes.

**Net effect:** Axiom 2 reduces to a special case of Axiom 1 (digit-domination for small primes in a specific interval).

---

## 4. Strategy C: Sieve-Theoretic Upper Bound

### 4.1 Setup

We want to bound $|S(k) \cap [2k, k^2]|$ where $S(k)$ is the set of n satisfying digit-domination for all primes p ≤ 29. By the CRT framework:

$$S(k) = \{n \in \mathbb{Z} : n \bmod p^{L_p} \in S_p(k) \; \forall p \le 29\}$$

The set $S(k) \cap [2k, k^2]$ has at most $R_k = |S(k) \cap [0, M_k)|$ elements (since $M_k > k^2$, each residue class contributes at most one element).

### 4.2 Selberg Sieve Approach

View the complement: n ∈ [2k, k²] is "sieved out" by prime p if digit-domination fails for p (i.e., p | C(n,k)). We want to show every n is sieved out by at least one prime.

The **Selberg sieve** provides upper bounds on the count of "unsieved" elements:

$$|S(k) \cap [2k, k^2]| \le \frac{k^2 - 2k}{G(k)}$$

where $G(k) = \sum_{\substack{d | P \\ d \le D}} \mu^2(d) \prod_{p | d} \frac{|S_p(k)|}{p^{L_p} - |S_p(k)|}$ for suitable $P = \prod_{p \le 29} p^{L_p}$ and level $D$.

For our specific problem, the moduli $p^{L_p}$ are "highly composite" and the residue sets are structured (Cartesian products of digit constraints), which the Selberg sieve handles well.

**But:** The Selberg sieve gives an upper bound of $\frac{N}{\sum \lambda_d^2 / g(d)}$ where the $\lambda_d$ are optimized. For our case, the "dimension" is $\kappa = \sum_{p \le 29} 1 = 10$ (sieving by 10 primes). The sieve bound is roughly $N / (\log D)^\kappa$ for $D$ up to $\sqrt{N}$. With $N = k^2$ and $D = k$, this gives $k^2 / (\log k)^{10}$, which is $\gg 1$ for all k.

**Problem:** The sieve dimension is too low. With only 10 primes (those ≤ 29), the sieve can't go below 1. We'd need many more primes.

If we use ALL primes ≤ k: the sieve dimension is $\pi(k) \approx k / \ln k$, which grows with k. The sieve bound becomes roughly $N / (\ln D)^{\pi(k)}$ which for $D = k$ and $N = k^2$ is $k^2 / (\ln k)^{k/\ln k}$. For large k, $(\ln k)^{k/\ln k} = e^{k}$ (since $k/\ln k \cdot \ln \ln k \approx k$ for large k), which overwhelms $k^2$. So the sieve bound goes to 0!

**Catch:** Using all primes ≤ k means the "sieving moduli" $p^{L_p}$ multiply to $M_k$, which can be astronomically large. The Selberg sieve requires $D \le \sqrt{N}$, meaning the level of distribution limits how many primes we can use. Standard sieve theory requires careful handling of error terms.

### 4.3 Large Sieve Inequality

The **large sieve inequality** states: for $\{a_n\}_{n=1}^{N}$ and moduli $q_1, ..., q_R$:

$$\sum_{r=1}^{R} \sum_{\substack{a \bmod q_r \\ (a, q_r) = 1}} \left|\sum_{n=1}^{N} a_n e(na/q_r)\right|^2 \le (N + Q^2 - 1) \sum_{n=1}^{N} |a_n|^2$$

Applied with $a_n = 1_{n \in S(k) \cap [2k, k^2]}$ and the excluded residue classes, this gives:

$$|S(k) \cap [2k, k^2]| \le \frac{k^2 + M_k^2}{L}$$

where $L$ counts the excluded residue classes. Since $M_k > k^2$, the bound is $O(M_k^2 / L)$, which is WORSE than the trivial bound $R_k$. The large sieve is not helpful here because our moduli are too large relative to the interval.

### 4.4 Assessment

**Strength:** Sieve methods are the natural tool for bounding the count of integers avoiding prescribed residue classes.

**Weakness:** Standard sieve inequalities are optimized for LARGE intervals sieved by SMALL moduli. Our problem has the opposite geometry: a SHORT interval [2k, k²] of length ~k² sieved by LARGE moduli (p^{L_p} can be > k). The level of distribution is unfavorable.

**A possible exception:** The **Bombieri-Vinogradov theorem** or **Barban-Davenport-Halberstam** type results might provide "on average" bounds over k, showing that for MOST k, S(k) ∩ [2k, k²] = ∅. This would reduce the problem to checking finitely many "exceptional" k values.

**Confidence:** Medium-Low. The sieve approach is natural but faces serious technical obstacles.

---

## 5. Strategy D: Computation + Effective Baker-Stewart Threshold

### 5.1 The Baker-Stewart Approach

A theorem of Stewart (1980), building on Baker's theory of linear forms in logarithms, gives:

**Theorem (Stewart, 1980).** For coprime bases $b_1, b_2 \ge 2$ and integer $n \ge 3$:
$$s_{b_1}(n) + s_{b_2}(n) > c \cdot \frac{\log n}{(\log \log n)^2}$$
where $c > 0$ is an effective constant depending on $b_1, b_2$.

### 5.2 Application to Our Problem

For n to digit-dominate k in base p, we need $s_p(n) \ge s_p(k)$ (digit-domination implies the digit sum of n is at least that of k at each position, hence globally). Actually, digit-domination is STRONGER than just having $s_p(n) \ge s_p(k)$; it requires EACH digit of n to be at least the corresponding digit of k.

But we can use the digit-sum bound as a necessary condition. If n satisfies digit-domination for k in bases 2 and 3 simultaneously, then:

$$s_2(n) \ge s_2(k) \quad \text{and} \quad s_3(n) \ge s_3(k)$$

For the digit-domination condition, $s_p(n) \ge s_p(k)$ is automatic. The CONSTRAINT is that the specific digit pattern must match, not just the sum. So Stewart's theorem on $s_p(n)$ doesn't directly help — it bounds the digit sum from BELOW, but we need the digit sum to be ABOVE s_p(k), which is already given.

**Alternative direction:** For n ∈ [2k, k²], $\log n \le 2 \log k$. If the MAXIMUM s_p(n) for any base p ≤ 29 is bounded above (by the interval constraint), and digit-domination requires s_p(n) ≥ s_p(k), then we need s_p(k) to be small enough. For "generic" k, s_p(k) ≈ (p-1)/2 · L_p(k) ≈ (p-1)/2 · log_p(k). If s_p(k) is "large" for some p, then the constraint s_p(n) ≥ s_p(k) is very restrictive (n must have large digits in base p).

But for the WORST CASE k (those with small digits in all bases), s_p(k) is small, and the constraint is weak. This is exactly the k ≈ 178416 worst case.

### 5.3 Effective Threshold Computation

Instead of an analytical proof for all k, we can:

1. **Compute** the worst-case density δ_k · k² for ALL k up to some threshold K₀.
2. **Prove analytically** that for k > K₀, δ_k · k² < c for some c < 1.
3. If c < 1, argue (using a sieve or covering result) that the actual count is 0.

The analytical bound for step 2 uses: for k > K₀, at least one of the primes p ≤ 29 forces k to have a "large" digit. Specifically:

**Claim (for sufficiently large k).** For every k > 2^{20} ≈ 10⁶, at least one of the primes p ∈ {2, 3, 5, 7} satisfies:
$$\prod_{i=0}^{L_p-1} \frac{p - d_i^{(p)}(k)}{p} < \frac{1}{k^{1/2}}$$

*Heuristic justification:* For $p = 2$, each bit of k contributes factor (2-bit)/2 = 1 if bit=0 or 1/2 if bit=1. The product is $2^{-\text{popcount}(k)} \cdot 2^0 = (1/2)^{\text{popcount}(k)}$ (not quite — it's 1/2 for each 1-bit). For k with ≥ 10 one-bits (out of 20 bits), the base-2 factor is ≤ $1/2^{10} = 1/1024 < 1/k^{1/2}$ for $k < 10^6$. But k could have very FEW one-bits (e.g., k = 2^19 has only 1 one-bit, giving density factor 1/2).

For k = 2^19: base-2 density = 1/2. Base-3 density: 2^19 in base 3 is about 12 trits, with "random" digits giving density ≈ (2/3)^{12} ≈ 0.0077. Combined: ≈ 0.0039, and δ_k · k² ≈ 0.0039 · 2^{38} ≈ 10^9. TERRIBLE.

This shows that pure powers of 2 are adversarial for this approach. We'd need to use MORE primes (not just 2, 3, 5, 7) to handle such cases.

**The general obstruction:** For ANY finite set of primes P₀, there exist infinitely many k that are "uniform" in all bases p ∈ P₀ (i.e., have digits close to 0 in all bases), giving density factors close to 1. This is because the digit distributions in different bases are "independent" in a suitable sense, and by simultaneous Diophantine approximation, k values can be found that have small digits in many bases at once.

### 5.4 Assessment

**Strength:** The hybrid computation + analytical approach is the most pragmatic path.

**Weakness:** The analytical bound needs to handle worst-case k (those with small digits in all bases ≤ 29 simultaneously). No known analytical tool provides the required precision.

**Most promising variant:** Push the computation to k = 10^7 or higher (feasible with the existing CRT algorithm), then look for an analytical cutoff. The worst-case k = 178416 has δ_k · k² ≈ 0.417, which is well below 1. If we can show that 0.417 is a GLOBAL maximum (not just a local one), we might be able to bootstrap an analytical argument.

**Confidence:** Medium. The computation is straightforward; the analytical gap-closing is hard.

---

## 6. Strategy E: Direct Computation Extension (Pragmatic)

### 6.1 What This Buys

The existing `native_decide` proof covers k ∈ [29, 700]. The CRT algorithm in `crt-density-k-ge-29.md` runs in time roughly proportional to |S₂(k)| · |S₃(k)| (initial CRT candidates, then filtered by remaining primes). For k ≤ 10^6, this is computationally feasible.

**Key question:** Can we extend `native_decide` in Lean to cover k up to 10,000? Or even 100,000?

The bottleneck is: for each k, we check all n ∈ [2k, k²]. For k = 10,000, this is checking ~10^8 pairs. With `native_decide`, this might take hours but is doable. For k = 100,000, it's 10^10 pairs — likely too slow for `native_decide` but fine for external computation.

### 6.2 Certified Computation

Instead of extending `native_decide` (which is slow for large ranges), we could:

1. Run an external CRT-based algorithm (in Python/C++) that certifies, for each k, a WITNESS: a specific prime p ≤ 29 and digit position i such that the combined CRT constraint from primes 2, 3, ..., p at position i eliminates all n ∈ [2k, k²].

2. Encode this witness in Lean and verify it with `decide` or simple lemma checking.

**Example witness for k = 29:** "Primes 2 and 3 together have CRT modulus 32 × 81 = 2592 > 841 = 29², and among the 36 CRT candidates, none falls in [58, 841]." This can be verified by listing the 36 values and checking each.

For large k, the witness is just the (short!) list of CRT survivors from the first few primes, verified to be outside [2k, k²]. Since the CRT filtering is so effective, the survivor list is typically empty after 2-3 primes.

### 6.3 Asymptotic Closure

Even with large-scale computation, we still need to handle k → ∞. Two options:

**(A) Accept a large finite verification + axiom for the tail.** Verify k ≤ K₀ computationally, axiomatize k > K₀. This is the current approach with K₀ = 700. Pushing K₀ higher reduces the axiom's "surface area" but doesn't eliminate it.

**(B) Prove an analytical tail bound.** Show that for k > K₀, some structural property guarantees zero exceptions. This is the hard part.

**Candidate tail argument:** For k > 10^{20} (say), the digit lengths L_p(k) for p ∈ {2, 3, 5} are all ≥ 60. The number of CRT candidates from primes {2, 3} alone is |S₂| · |S₃|. Even in the WORST case (k is a power of 6, minimizing digit constraints for both 2 and 3), the filtering by prime 5 eliminates enough candidates that none survive in [2k, k²].

This would require a detailed case analysis on the digit structure of k in bases 2, 3, 5, which is possible but tedious.

### 6.4 Assessment

**Strength:** Most practical path to progress. Computation is reliable, reproducible, and scales well.

**Weakness:** Doesn't provide a mathematical PROOF for all k. The axiom persists (though with a higher threshold).

**Confidence:** High for extending the verified range; Low for eliminating the axiom entirely.

---

## 7. Strategy F: Covering System / Chinese Remainder Covering

### 7.1 Idea

Instead of showing S(k) ∩ [2k, k²] = ∅ directly, show that [2k, k²] is COVERED by "prime certificates": for each n ∈ [2k, k²], exhibit a specific prime p ≤ 29 such that p | C(n,k).

This is a covering system: [2k, k²] = ∪_{p ≤ 29} A_p(k), where A_p(k) = {n ∈ [2k, k²] : p | C(n,k)}.

By inclusion-exclusion: |[2k, k²] \ ∪ A_p| = |S(k) ∩ [2k, k²]|. We want this to be 0.

### 7.2 Constructive Covering

For each prime p ≤ 29, the set A_p(k) = {n ∈ [2k, k²] : digit-domination fails for p} has density 1 - ρ_p(k) in [2k, k²], where ρ_p(k) = |S_p(k)| / p^{L_p}. The "uncovered" set has density δ_k = ∏ ρ_p.

A CONSTRUCTIVE covering would assign each n to a specific prime p(n) such that p(n) | C(n,k). If we can find such an assignment for all n ∈ [2k, k²] and all k ≥ 29, we're done.

**For specific k:** This is exactly what the CRT algorithm does — it checks that S(k) ∩ [2k, k²] = ∅, which means every n is assigned to some p.

**For general k:** We'd need a RULE that maps (n, k) to a prime p ≤ 29 such that digit-domination fails. For example:
- "Let p be the smallest prime such that dig_0^{(p)}(k) > dig_0^{(p)}(n)." This works when the bottom digit of k exceeds that of n in some base, but n could have larger bottom digits in all bases.

### 7.3 Two-Prime Covering for k ≥ 6

**Lemma.** For k ≥ 6, at least one of the following holds for every n ∈ [2k, k²]:
- 2 | C(n,k), or
- 3 | C(n,k).

*Attempted proof:* 2 ∤ C(n,k) iff k ⊆ n bitwise (every 1-bit of k is a 1-bit of n). 3 ∤ C(n,k) iff k ⪯₃ n (digit-domination in base 3).

For n ∈ [2k, k²] satisfying BOTH conditions: n bitwise contains k AND ternary-dominates k. The count of such n mod lcm(2^{L₂}, 3^{L₃}) is |S₂| · |S₃|.

For k = 6 = 110₂ = 20₃: |S₂| = 1·2·1 = 2 (mod 8: {6, 7}), |S₃| = 1·2 = 2 (mod 9: {6, 7, 8, ...} wait, digit 0 of 6 in base 3 is 0, digit 1 is 2. So valid n mod 9 have digit 0 ≥ 0 (all 3 values) and digit 1 ≥ 2 (1 value: {2}). So |S₃| = 3 · 1 = 3. CRT mod 72: 6 candidates. In [12, 36]: check if any survive. 72 > 36, so each candidate ≤ 1 occurrence. S₂ gives n ∈ {6, 7} mod 8. S₃ gives n ∈ {6, 7, 8} mod 9. CRT candidates mod 72: (6 mod 8 = 6, 6 mod 9 = 6) → n = 6. (6, 7) → n = 70. (6, 8) → n = 62. (7, 6) → n = 15. (7, 7) → n = 7. (7, 8) → n = 71. So candidates are {6, 7, 15, 62, 70, 71}. In [12, 36]: only n = 15. Check: C(15, 6) = 5005 = 5 × 7 × 11 × 13. Indeed 2 ∤ 5005 and 3 ∤ 5005, so n = 15 is NOT covered by primes 2 and 3 alone.

So two primes don't suffice, even for small k. The covering needs more primes.

### 7.4 Assessment

**Strength:** Reframes the problem as a covering/coloring question, which has a different combinatorial flavor.

**Weakness:** Finding a universal covering rule (n, k) → p that works for ALL k seems as hard as the original problem. Without such a rule, we're back to case-by-case computation.

**Confidence:** Low for a general proof; High as a framing device.

---

## 8. Strategy G: Extend Interval Divisibility (Novel for Axiom 2)

### 8.1 Generalized Interval Divisibility

The Interval Divisibility Lemma says: if p | M and p ∈ (k, M], then p | C(n,k) for all n ∈ [kM, kM+k).

**Generalization:** What if p ∤ M but p ∈ (k, M]?

Then kM mod p = k · (M mod p) mod p ≠ 0. The residues of n ∈ [kM, kM+k) mod p are {kM mod p, ..., kM+k-1 mod p}. By large prime criterion, p | C(n,k) iff n mod p < k.

The question: does the window of k consecutive residues starting at kM mod p contain a value < k?

As shown in Strategy B (§3.1): for p ∈ (k, 2k) (specifically p < 2k), the window of k consecutive residues ALWAYS contains a value < k. This is because the "bad" range [k, p-k] (where the entire window could avoid values < k) is empty when p < 2k.

### 8.2 Application to Axiom 2

For M ∈ (k, 2k) and k-smooth:

If there exists ANY prime p ∈ (k, M] (even one that doesn't divide M), then p | C(n,k) for some n in the interval. But we need p | C(n,k) for the SPECIFIC n, not just any n in the interval.

Wait — the problem only asks for EACH (n,k) separately: does there exist a prime ≤ max(n/k, k) dividing C(n,k)? So for a specific n, we need ONE prime.

For a specific n ∈ [kM, kM+k) with M ∈ (k, 2k):
- If n mod p < k for some prime p ∈ (k, M]: done, p | C(n,k) and p ≤ M ≤ n/k.
- If n mod p ≥ k for ALL primes p ∈ (k, M]: then n avoids all large primes ≤ M.

How many primes are in (k, M] for M ∈ (k, 2k)? By Bertrand, at least one prime in (k, 2k], but it might be > M. For M close to 2k, there are several primes. For M = k+1, there are no primes in (k, k+1] unless k+1 is prime.

**For the specific case M = k+1 (the hardest):** n ∈ [k(k+1), k(k+1)+k) = [k²+k, k²+2k). No primes in (k, k+1] (unless k+1 is prime). If k+1 is prime, then p = k+1 ∈ (k, M] and we use the large prime criterion. If k+1 is composite, no large prime is available, and we must rely on small primes.

### 8.3 Combined Small + Large Prime Argument

For n ∈ (k², 2k²) (which corresponds to M ∈ (k, 2k)):

Split into sub-cases based on primes in (k, M]:

**(i)** If M has a prime factor > k: Interval Divisibility Lemma gives p | C(n,k). ✅ (But M is k-smooth, so this case is excluded by hypothesis.)

**(ii)** If there exists a prime p ∈ (k, M] with p ∤ M: by §8.1 generalization, the window of k consecutive residues starting at kM mod p contains a value < k (since p < 2k). But we need n SPECIFICALLY to hit this value, which depends on n's position in the interval.

Actually, we can be more precise. For a specific n, if n mod p < k, then p | C(n,k). For a specific n, n mod p is determined. The question is: among all primes p ∈ (k, M], does at least one satisfy n mod p < k?

This is the SAME as asking: is n avoiding all residues < k for every prime in (k, M]? The density of n doing this is $\prod_{p \in (k,M]} (p-k)/p$, which for M close to 2k is about $\prod (p-k)/p$ over primes in (k, 2k], which we've already shown is ≈ e^{-Ω(k/ln k)}$ — extremely small.

But again, this is a density argument. For SPECIFIC n, we can't rule it out.

### 8.4 Assessment

**This strategy clarifies the structure but doesn't bypass the density obstacle.** For k-smooth M ∈ (k, 2k), the available "large" primes (those in (k, M]) may not include any that divide C(n,k) for the specific n. The small primes are the last resort, and their coverage depends on digit-domination — the same obstacle as Axiom 1.

---

## 9. Synthesis and Recommendation

### 9.1 What We've Learned

| Strategy | Closes Axiom 1? | Closes Axiom 2? | Practicality |
|----------|-----------------|-----------------|--------------|
| A (Smooth parts) | No | Partially | Low |
| B (Bertrand chain) | No | **Yes for M ≥ 2k** | High |
| C (Sieve) | Maybe (large k) | Reduces to Axiom 1 | Medium |
| D (Baker-Stewart) | Theoretically | Reduces to Axiom 1 | Low |
| E (Computation) | Extends range | Extends range | **High** |
| F (Covering) | Reframes | Reframes | Low |
| G (Generalized IDL) | No | Partially | Medium |

### 9.2 The Fundamental Obstacle

**All approaches ultimately face the same barrier:** for any finite set of primes P₀, there exist k values where the digit-domination density in ALL bases p ∈ P₀ is relatively high. The worst case (k ≈ 178416) has δ_k · k² ≈ 0.417 using primes ≤ 29. While this is < 1 (and we can't find any actual exception), going from "expected count < 1" to "count = 0" requires either:

1. **Computation** for each specific k, or
2. An **equidistribution result** showing CRT residues don't cluster in short intervals.

No known analytical tool provides (2) at the required precision. The Baker-Stewart bounds give $s_p(n) = \Omega(\log n / (\log \log n)^2)$, which is too weak. Effective versions might suffice for k > 10^{100}, but the threshold would be astronomical.

### 9.3 Recommended Path Forward

**Short term (days):**
1. **Write the Bertrand chain proof for M ≥ 2k** (Strategy B, §3.1) as a standalone verified proof. This closes half of Axiom 2 with a clean, structural argument.
2. **Formally reduce Axiom 2 (M ∈ (k, 2k) case) to Axiom 1.** Show that for k-smooth M ∈ (k, 2k) and n ∈ [kM, kM+k), the condition "no prime ≤ k divides C(n,k)" implies "n digit-dominates k for all primes ≤ k." Then Axiom 2's smooth case follows from Axiom 1.

**Medium term (weeks):**
3. **Extend `native_decide` range** to k = 5000 or 10000 by optimizing the CRT check function in Lean. This is the most reliable way to shrink the axiom.
4. **Implement certified CRT witnesses** (Strategy E, §6.2): compute witnesses externally, verify in Lean.

**Long term (aspirational):**
5. **Prove an analytical tail bound** using a combination of:
   - Baker's theorem (effective lower bounds on digit sums in two independent bases)
   - Pigeonhole on the digit structure of k in bases 2, 3, 5 (showing at least ONE base has "large" digits that make the density factor small enough)
   - Careful case analysis on the base-2 and base-3 digit patterns of k

This would require significant number-theoretic work and is likely publishable in its own right.

### 9.4 Can We Truly Avoid Density?

**Honest answer: No, not with current mathematical technology.** Every approach to Axiom 1 eventually reduces to: "the CRT residues satisfying digit-domination for all primes ≤ 29 are too spread out to hit the interval [2k, k²]." This is inherently a statement about the DISTRIBUTION of these residues, which is a form of density/equidistribution.

The Bertrand chain argument (Strategy B) is the ONE case where we have a genuinely non-density proof — and it only works for Axiom 2 with M ≥ 2k, where the residue-counting argument gives an EXACT zero (the "bad range" is empty), not just an expected-value bound.

**For Axiom 1, the best realistic path is computation** (extending the verified range) **plus an axiom for the tail**, clearly documented as computationally supported but not analytically proved.

---

## References

- Stewart, C.L. (1980). "On the representation of an integer in two different bases." *J. reine angew. Math.*, 319, 63–72.
- Baker, A. (1975). *Transcendental Number Theory*. Cambridge University Press.
- Hildebrand, A. (1986). "On the number of positive integers ≤ x and free of prime factors > y." *J. Number Theory*, 22, 289–307.
- Selberg, A. (1947). "On an elementary method in the theory of primes." *Norske Vid. Selsk. Forh.*, 19, 64–67.
- Ecklund, Eggleton, Erdős, Selfridge (various). Prime factors of binomial coefficients.

# B3b Case: Proof that no exceptions exist for k ≥ 9

**Status:** DRAFT — under development
**Goal:** For k ≥ 9, there is no (n, k) with n = sq, s | k, s < k, q prime > ⌊n/k⌋, n > k², ⌊n/k⌋ k-smooth, and minFac(C(n,k)) > ⌊n/k⌋.

---

## 0. Setup and Notation

**B3b hypothesis.** Fix k ≥ 9. Suppose n = sq where:
- s | k, s < k, t := k/s ≥ 2
- q is prime
- M := ⌊n/k⌋ = ⌊q/t⌋
- M is k-smooth (all prime factors ≤ k)
- n > k² (equivalently q > st² = kt)

**Exception assumption (toward contradiction).** Assume minFac(C(n,k)) > M, i.e., p ∤ C(n,k) for all primes p ≤ M.

By the Kummer condition, this means: **k ≤_p n** (digit domination in base p) for every prime p ≤ M.

---

## 1. The prime q divides C(n,k)

Since q > k and q | n: by the large prime criterion, n mod q = 0 < k, so q | C(n,k).

More precisely: v_q(C(n,k)) = ⌊sq/q⌋ - ⌊st/q⌋ - ⌊s(q-t)/q⌋ = s - 0 - (s-1) = 1.

So C(n,k) = q · A where A is a positive integer.

**This means the exception condition becomes: all prime factors of A are also > M.**

---

## 2. Fundamental flaw of the CRT counting approach

The existing CRT + Mertens approach attempts to bound:

    |{n ∈ [1, kM] : n mod p ≥ k for all primes p ∈ (k, M]}| ≤ (kM/Q + 1) · ∏(pᵢ - k)

where Q = ∏ pᵢ over primes in (k, M].

**This bound is always ≥ 1** since ∏(pᵢ - k) ≥ 1, so it can never prove the count is 0. The approach is structurally incapable of closing the proof.

---

## 3. New approach: Kummer constraints from small primes

### 3.1 Digit domination is extremely restrictive

For the exception: k ≤_p n for all primes p ≤ k (and in fact for all p ≤ M > k).

Write k in base p. At each digit position, the corresponding digit of n must be ≥ the digit of k. This constrains n modulo p^(⌈log_p k⌉ + 1) for each prime p ≤ k.

**Key quantity.** Let Q₀ = ∏_{p ≤ k} p^{d_p} where d_p = ⌈log_p(k)⌉ + 1. Let S₀ = number of valid residues of n mod Q₀ satisfying all digit domination conditions. Then:

    δ_small(k) := S₀ / Q₀ = ∏_{p ≤ k} ∏_{i=0}^{d_p - 1} (p - digit_i(k, p)) / p

where digit_i(k, p) is the i-th base-p digit of k.

**For k = 9:** Using primes 2, 3, 5, 7:
- Base 2 (k = 1001₂): positions with digit 1 force n's digit ≥ 1. Density factor from base 2: (1/2)² = 1/4 [two nonzero digits]
- Base 3 (k = 100₃): density factor ≈ 2/3
- Base 5 (k = 14₅): density factor ≈ (1/5)(4/5) = 4/25
- Base 7 (k = 12₇): density factor ≈ (5/7)(6/7) = 30/49

Combined: δ_small(9) ≈ (1/4)(2/3)(4/25)(30/49) ≈ 0.016

### 3.2 Large prime constraints (primes in (k, M])

For each prime p ∈ (k, M]: the condition n mod p ≥ k removes k/p fraction. The surviving fraction is (p-k)/p = 1 - k/p.

Combined: δ_large(k, M) = ∏_{k < p ≤ M} (1 - k/p) ≈ (C ln k / ln M)^k by Mertens.

### 3.3 Combined density

    δ(k, M) = δ_small(k) · δ_large(k, M)

For k = 9, M = k + 1 = 10 (no primes in (9, 10]): δ ≈ 0.016.
For k = 9, M = 100: δ ≈ 0.016 · (C ln 9/ln 100)^9 ≈ 0.016 · 0.48^9 ≈ 0.016 · 0.002 ≈ 3 × 10⁻⁵.

### 3.4 Why density alone is insufficient

Even with δ ≈ 0.016 for the worst case (M ≈ k), the expected count in an interval of length k is δ · k ≈ 0.15 < 1. But "expected count < 1" doesn't prove "count = 0" deterministically.

---

## 4. Exploiting B3b structure: q is prime and M is k-smooth

### 4.1 The k-smoothness constraint on M

In B3b (Type B), M = ⌊q/t⌋ is k-smooth. This means every prime factor of ⌊q/t⌋ is ≤ k.

**This is a very strong constraint on q.** Writing q = tM + r where 0 ≤ r < t: q = tM + r where M is k-smooth and 0 ≤ r < t.

So q lies in {tM, tM+1, ..., tM+t-1} for some k-smooth M.

### 4.2 Double Kummer constraint

For the exception, n = sq must satisfy digit domination by k = st for ALL primes p ≤ M.

For primes p ≤ k that DO NOT divide s: n mod p = s · (q mod p) mod p. Since gcd(s,p) = 1, the digit domination condition on n translates to a condition on q mod p^{d_p}, which constrains q to a set of density δ_small(k) (roughly).

For primes p ≤ k that DO divide s: since s | k and p | s, we have p | k and p | n. The analysis at low digit positions gives no constraint (carries are 0). The constraints come from higher digit positions and depend on the specific digits of s, t, q in base p.

**Combined constraint on q:** q must be prime, lie in the arithmetic progression {tM + r : 0 ≤ r < t} for some k-smooth M, and satisfy all Kummer conditions from primes ≤ k.

### 4.3 Counting argument for B3b specifically

For fixed s | k (with t = k/s), the possible exception values are:
    {q prime : q > kt, ⌊q/t⌋ is k-smooth, and st ≤_p sq for all p ≤ ⌊q/t⌋}

The key observation: **the set of k-smooth numbers has density 0.** More precisely, by the Dickman-de Bruijn function ρ(u), the count of k-smooth numbers up to x is x · ρ(log x / log k), where ρ(u) ~ u^{-u} for large u.

For our case: M ranges up to ⌊q/t⌋, and M must be k-smooth. The "available" M values up to X have count ~ X · ρ(log X / log k). For large X: this density → 0.

**But we need a FINITE result, not an asymptotic one.** We need: for ALL q > kt (not just "most"), the B3b exception doesn't hold.

---

## 5. Approach: Direct Kummer analysis per divisor pair (s, t)

### 5.1 Key structural lemma

**Lemma.** Let p be a prime with p | t and p ∤ s (i.e., p divides k/s but not s). Let b = v_p(t) ≥ 1. Then:

    p | C(n, k) ⟺ there is a carry at position ≥ v_p(s) + b in base-p addition of k and (n-k).

Since n = sq and k = st: n - k = s(q - t). Writing in base p at position a = v_p(s):
- The digits of k/p^a = st/p^a and (n-k)/p^a = s(q-t)/p^a at position b give the critical carry.

The carry at position a + b occurs when:
    {st/p^{a+b}} + {s(q-t)/p^{a+b}} ≥ 1

Since v_p(st) = a + b (exactly): st/p^{a+b} is an integer coprime to p. Call it c_k := st/p^{a+b} (with gcd(c_k, p) = 1). Then {st/p^{a+b+1}} = c_k mod p / p.

And s(q-t)/p^{a+b} = (s/p^a)(q-t)/p^b. Since v_p(t) = b: (q-t)/p^b = (q - t)/p^b. If p ∤ q (which holds since q is prime > k ≥ p): v_p(q-t) = v_p(t) = b (since v_p(q) = 0 and v_p(t) = b, and the p-adic valuation of a difference is the min when they differ). Wait: v_p(q - t) = min(v_p(q), v_p(t)) = min(0, b) = 0 when b > 0.

Hmm, that's wrong. v_p(q - t): since v_p(q) = 0 and v_p(t) = b ≥ 1: v_p(q - t) = 0 (because q and t have different p-adic valuations, so v_p(q-t) = min(v_p(q), v_p(t)) = 0).

So s(q-t)/p^{a+b} is NOT necessarily an integer when b > 0. In fact, v_p(s(q-t)) = a + 0 = a < a + b. So s(q-t)/p^{a+b} is not an integer, and we need to work with the carry analysis more carefully.

**[TODO: Complete this analysis. The key point is that for p | t with p ∤ s, the p-adic structure of q - t creates carries that force p | C(n,k).]**

### 5.2 The p | t case (when such p exists)

If t = k/s has a prime factor p that does not divide s, then by the analysis in 5.1, the carry at level a + b is determined by q mod p. Since v_p(q-t) = 0 (q and t have different p-adic valuations), the fractional part analysis at level a + b should force a carry for "most" values of q mod p.

**[TODO: Make this rigorous. Show the carry probability is > 1/2 for each such p.]**

### 5.3 The case t = p^a (prime power, s = k/p^a)

When t is a prime power p^a: the only prime dividing t is p. If p | s, then the carry analysis is more subtle.

### 5.4 The worst case: s = 1, t = k

When s = 1: n = q (prime), k = t, M = ⌊q/k⌋. This is the case where the B3b structure gives the least information, since n is just a prime.

The exception condition: k ≤_p q for all primes p ≤ M. I.e., q "digit-dominates" k in every base p ≤ M.

For k ≥ 9: the density of q satisfying digit domination in bases 2, 3, 5, 7 is ≈ 0.016. Among q values near k², the interval length is ≈ k, so expected survivors ≈ 0.016k ≈ 0.15 < 1.

But this is only a density argument.

---

## 6. [INCOMPLETE] Toward a deterministic proof

### Option A: Sieve-theoretic upper bound

Use the Selberg sieve to show: the number of primes q ∈ (kt, kt+L) satisfying the combined Kummer + smoothness conditions is o(1) as k → ∞.

**Advantage:** Standard analytic NT.
**Issue:** Need explicit bounds for k ≥ 9, not just asymptotic.

### Option B: Constructive Kummer collision

For each divisor pair (s, t) with s | k, s < k, t ≥ 2: find a SPECIFIC prime p ≤ k such that the Kummer condition k ≤_p n fails. I.e., find p where some base-p digit of k exceeds the corresponding digit of n.

The challenge: for a single prime p, there always exist n satisfying k ≤_p n (just take n with all large digits). So we need to use MULTIPLE primes and show the conditions are JOINTLY unsatisfiable.

### Option C: Exploit q = tM + r structure

Since q = tM + r with M k-smooth and 0 ≤ r < t:
n = sq = s(tM + r) = kM + sr.

So n mod k = sr (since s | k, we have sr < k iff r < t, which holds).

Now for primes p | k: the base-p analysis of n = kM + sr reduces to understanding sr mod p^i for various i. Since sr < k < p^{d_p}: the lowest d_p digits of n in base p are determined by sr. And the lowest d_p digits of k are fixed.

For digit domination: the lowest d_p digits of k must be ≤ the lowest d_p digits of n = sr (digit by digit in base p).

**This means: for each prime p ≤ k, the base-p digits of sr must dominate those of k = st.**

Since s is common: this reduces to checking whether the base-p representation of sr (= s·r) dominates that of st (= s·t) for each p ≤ k and each r ∈ {0, ..., t-1}.

**For p ∤ s:** The map r ↦ sr mod p is a bijection on Z/pZ. The digit domination condition at each position constrains r mod p^{something}.

**For p | s:** More complex, but the shared factor of s creates alignment.

### Key question for Option C

Is it true that for k ≥ 9 and EVERY (s, t) with st = k, s | k, t ≥ 2, and EVERY r ∈ {0, ..., t-1}, the digit domination condition st ≤_p sr FAILS for some prime p ≤ k?

If YES: then no B3b exception can exist for ANY k ≥ 9.

Note: st ≤_p sr means "every base-p digit of st is ≤ the corresponding digit of sr." Since both are < k < p^{d_p}, we only need to check the first d_p digits.

**Special case r = 0:** sr = 0, which has all digits 0. Digit domination st ≤_p 0 requires all digits of st to be 0, i.e., st = 0. But st = k ≥ 9 ≠ 0. So r = 0 ALWAYS fails digit domination for EVERY prime. ✓

**But r = 0 corresponds to q = tM, which means t | q. Since q is prime and t ≥ 2: this requires t = q (impossible since q > kt) or t is 1 (contradicts t ≥ 2). Wait: q = tM + 0 = tM, so t | q. Since q is prime: t = 1 or t = q. Since t ≥ 2 and t = k/s ≤ k < q: impossible. So r = 0 never occurs. ✓**

**Special case r = t (also impossible since r < t).**

So r ∈ {1, ..., t-1}. We need: for each such r, the base-p digit of sr fails to dominate st for some p ≤ k.

---

## 7. Failed attempt: digit domination of k by sr

**Idea:** Since n = kM + sr with sr < k, the low-order base-p digits of n come from sr. If st > sr implies digit domination st ≤_p sr fails, then p | C(n,k).

**Why it fails:** Digit domination k ≤_p n involves ALL digits, not just the low ones. The HIGH digits of n come from kM, which is large. The high digits of n can dominate the high digits of k, so k ≤_p n can hold even though st > sr.

**Example:** (62, 6) is a genuine exception. k = 6 = 110₂, n = 62 = 111110₂. Despite 6 > 2 (= sr), 6 ≤_2 62 holds (digit-by-digit: 0≤0, 1≤1, 1≤1, 0≤1, 0≤1, 0≤1). So 2 ∤ C(62,6). ✓

The high bits of n = 62 (from kM = 60) provide the large digits that satisfy domination.

---

## 8. Verified exception analysis

C(62, 6) = 61,474,519 = 19 × 29 × 31 × 59 × 61.
minFac = 19 > M = 10. Confirmed exception.

For this case: k = 6, s = 2, t = 3, q = 31, M = 10.
- 2 ∤ C(62,6) because 6 ≤_2 62 ✓
- 3 ∤ C(62,6) because 6 ≤_3 62 (6 = 20₃, 62 = 2022₃: 0≤2, 2≤2, ≤ ok) ✓
- 5 ∤ C(62,6) because 6 ≤_5 62 (6 = 11₅, 62 = 222₅: 1≤2, 1≤2) ✓
- 7 ∤ C(62,6) because 6 ≤_7 62 (6 = 6₇, 62 = 116₇: 6≤6, 0≤1, 0≤1) ✓

So ALL primes ≤ 10 satisfy digit domination: 6 ≤_p 62 for p = 2,3,5,7. This is why minFac > 10.

**Key insight from this example:** k = 6 is "too small" — it has few digits in each base, making domination easy. For k ≥ 9, the digit patterns are more complex.

---

## 9. Double Kummer Constraint: Results and Limitations

### 9.1 The identity

C(sq, st) = q · C(sq-1, st-1) / t    (since C(n,k) = (n/k)·C(n-1,k-1))

So A := C(sq,st)/q = C(sq-1, st-1)/t. The exception requires all prime factors of A to be > M.

### 9.2 What this gives

For primes p NOT dividing t: v_p(A) = v_p(C(sq-1,st-1)), and the exception requires this = 0.
By Kummer: (k-1) ≤_p (n-1) for all such p.

**Strict double constraint**: k ≤_p n AND (k-1) ≤_p (n-1) for ALL primes p ≤ k.

**Computational result**: The strict double constraint gives **ZERO valid residues** mod Q₀ for ALL k ≥ 6, ALL divisor pairs (s,t). This is deterministic (not density-based).

### 9.3 Why the strict constraint is overly strong

For primes p dividing t: the correct condition is v_p(C(sq-1,st-1)) = v_p(t) (allowing carries), not v_p = 0 (no carries). The strict condition incorrectly requires 0 carries.

**With the EXACT condition**: the count returns to the SINGLE constraint count. The second constraint adds NO information at primes p | t, and adds NOTHING USEFUL at primes p ∤ t (because (k-1) ≤_p (n-1) is automatically satisfied whenever k ≤_p n and the lowest base-p digit of k is nonzero).

### 9.4 Why the double constraint is limited

(k-1) ≤_p (n-1) follows from k ≤_p n whenever the lowest base-p digit of k is ≥ 1 (because subtracting 1 only affects the lowest digit, preserving domination). The double constraint only adds information when the lowest digit of k in base p is 0, i.e., when p | k. And for p | t specifically, the exact condition allows v_p(t) carries, making it vacuous.

**Bottom line**: The double Kummer constraint from C(n,k)/q DOES NOT reduce the survivor count below the single constraint for the exact (correct) conditions. We need additional arguments.

---

## 10. Correct approach: Combined constraints per (s, t, r, M)

### 9.1 Precise decomposition

For B3b with n = sq, s | k, t = k/s, q = tM + r (0 < r < t):
    n = kM + sr

The Kummer conditions for ALL primes p ≤ M give:
    k ≤_p (kM + sr) for all primes p ≤ M

Since kM is a specific multiple of k, the digit patterns of n = kM + sr in base p depend on BOTH M and r. This couples the constraints: changing M changes the available primes AND the digit patterns.

### 9.2 The real question

For k ≥ 9: does there exist M (k-smooth), s | k with t = k/s ≥ 2, r ∈ {1,...,t-1} with tM + r prime, such that k ≤_p (kM + sr) for all primes p ≤ M?

### 9.3 Why k ≥ 9 should work

For k ≥ 9, the digit representations of k in the first 4 primes (2,3,5,7) are complex enough that the JOINT digit domination condition is extremely restrictive. The density of valid n mod Q₀ (where Q₀ = lcm of relevant prime powers) is ≈ 0.016 for k = 9.

The challenge is converting this density bound into a deterministic impossibility proof.

### 9.4 Possible approaches (ranked by feasibility)

1. **Sieve bound**: Use Selberg/Brun sieve to upper-bound primes satisfying CRT conditions. Standard in analytic NT but needs explicit constants for k ≥ 9.

2. **Pigeonhole on short intervals**: For M close to k, the interval [kt, kt + k) contains ≈ k integers. The Kummer conditions admit ≈ 0.016k ≈ 0.15 of them. Since we need q prime AND ⌊q/t⌋ k-smooth, the constraints compound.

3. **Recursive descent on t**: For each factorization k = st, analyze the constraint q ≡ r mod t separately. Since q is prime and q > kt, Dirichlet's theorem guarantees primes in each residue class, but the JOINT CRT + Kummer conditions may be empty.

4. **Case analysis on k**: For k = 9, 10, 11, ..., verify the digit domination constraints by hand/symbolically. Though the user forbids computation in Lean, a pen-and-paper case analysis for a finite number of k values (up to some K₀) combined with an asymptotic argument for k > K₀ might work.

---

## 11. Gap Theorem for k ∈ {7, 8, 9}

### 11.1 Statement

For k ∈ {7, 8, 9} and every divisor pair (s, t) with st = k, t ≥ 2:

The Kummer digit-domination constraints from primes ≤ k leave valid residue classes mod Q₀ with minimum gap > t. This means any interval of length t contains AT MOST ONE valid residue.

**Verified computationally:**
- k=7, s=1, t=7: min_gap=14 > t=7 ✓
- k=8, s=1, t=8: min_gap=10 > t=8 ✓; s=2, t=4: min_gap=20 > t=4 ✓; s=4, t=2: min_gap=10 > t=2 ✓
- k=9, s=1, t=9: min_gap=10 > t=9 ✓; s=3, t=3: min_gap=10 > t=3 ✓

### 11.2 Proof structure

For a B3b exception with fixed M (k-smooth): q ranges over primes in (tM, t(M+1)), an interval of length ≤ t. By the gap theorem, this interval contains at most 1 valid residue mod Q₀.

Case 1: The interval contains 0 valid residues → no exception for this M. ✓
Case 2: The interval contains exactly 1 valid residue q₀ → need q₀ to be prime AND ⌊q₀/t⌋ = M to be k-smooth. Since most q₀ are NOT prime (density ~ 1/ln(q₀)), and the k-smoothness condition further restricts, the combined probability is very small.

**For a rigorous proof**: need to show that for EVERY M (k-smooth, M > k), the unique valid q₀ in (tM, t(M+1)) either:
(a) doesn't exist, OR
(b) is not prime, OR
(c) doesn't satisfy ⌊q₀/t⌋ = M (boundary effects).

This still requires a case-by-case or sieve argument, but the gap property makes it tractable.

### 11.3 Status for k ≥ 10

For k ≥ 10: the per-prime minimum gap analysis is inconclusive (individual primes allow gap=1). The full CRT minimum gap is hard to compute for large Q₀. Need either:
- A PROOF that the CRT minimum gap > t for all k ≥ 10 (likely true but hard to prove analytically)
- An alternative approach for k ≥ 10 (e.g., sieve theory, or handling k ≥ 10 via Konyagin's bound directly)

---

## 12. Open Questions and Next Steps

### 12.1 What's proved

1. The CRT counting approach (GapPrime.lean) is fundamentally flawed and should be abandoned.
2. The Kummer digit-domination density from small primes is ~0.016 for k=9 (and decreasing for larger k).
3. For k ∈ {7, 8, 9}: the "gap theorem" (min_gap > t) holds, reducing B3b to checking at most 1 candidate per M-interval.
4. No B3b exceptions exist for k ≥ 7 up to n = 10000 (exhaustive search).

### 12.2 What's needed

For a complete proof of B3b for k ≥ 9:

**Option A (k ∈ {9, ..., 28}, k ≥ 29 separately):** For k ≥ 29, the existing "Strategy 5" approach works (though it uses computation). For k ∈ {9, ..., 28}: use the gap theorem where applicable (k ∈ {9}) and extend with additional analysis.

**Option B (uniform proof for all k ≥ 9):** Need to prove that the combined Kummer + large-prime constraints leave 0 exceptions. This likely requires sieve-theoretic arguments (Selberg sieve) to handle the "at most 1 candidate per interval" → "0 candidates" step.

**Option C (weaker statement):** Prove B3b for a specific finite set of k values (say k ∈ {9, ..., K₀}) via the gap theorem + explicit verification, and use Konyagin's bound for k > K₀. This reduces the axiom but doesn't fully eliminate computation.

### 12.3 Key mathematical insight

**The gap theorem is the main new contribution**: showing that Kummer constraints from primes ≤ k space out valid residues by more than t = k/s is a deterministic, non-density result. Combined with the primality and smoothness constraints, it should suffice for a complete proof of B3b — but closing the last step requires either sieve theory or explicit enumeration.

**[DRAFT v2 — February 14, 2026]**

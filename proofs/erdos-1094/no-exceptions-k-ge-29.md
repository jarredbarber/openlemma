# No Exceptions Exist for $k \geq 29$

**Status:** Verified ✅
**Reviewed by:** erdos1094-gca (initial review), erdos1094-q3j (verified after dependencies)
**Statement:** For all integers $k \geq 29$ and $n \geq 2k$:
$$\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \max\!\left(\left\lfloor \frac{n}{k} \right\rfloor,\, k\right).$$
Equivalently, the exceptional set $E = \{(n, k) \mid 0 < k,\; 2k \leq n,\; \mathrm{minFac}(\binom{n}{k}) > \max(\lfloor n/k \rfloor, k)\}$ contains no pair $(n, k)$ with $k \geq 29$.
**Dependencies:** proofs/kummer-theorem.md, proofs/crt-density-k-ge-29.md, proofs/large-n-divisibility.md
**Confidence:** Certain

---

## 1. Notation and Setup

Throughout, $k$ and $n$ denote positive integers with $k \geq 29$ and $n \geq 2k$.

- $\binom{n}{k} = \frac{n!}{k!(n-k)!}$ is the binomial coefficient.
- $\mathrm{minFac}(m)$ is the smallest prime factor of $m$ (well-defined for $m \geq 2$).
- $\lfloor \cdot \rfloor$ denotes the integer floor function.

**Observation:** Since $k \geq 29 \geq 2$ and $n \geq 2k \geq 4$, we have $\binom{n}{k} \geq \binom{n}{2} = \frac{n(n-1)}{2} \geq 6$, so $\mathrm{minFac}\!\left(\binom{n}{k}\right)$ is well-defined.

We write $T(n,k) = \max(\lfloor n/k \rfloor, k)$ for the threshold appearing in the conjecture.

**Goal:** Show there exists a prime $p \leq T(n,k)$ with $p \mid \binom{n}{k}$.

---

## 2. The Two Dependencies

We use two results, proved separately:

### Result 1: No digit-domination survivors in $[2k, k^2]$ (proofs/crt-density-k-ge-29.md)

*For every integer $k \geq 29$, there is no integer $n \in [2k, k^2]$ such that $k \preceq_p n$ (digit-domination) holds for all primes $p \leq 29$.*

**Contrapositive form:** For every $k \geq 29$ and every $n \in [2k, k^2]$, there exists a prime $p \leq 29$ such that digit-domination $k \preceq_p n$ fails.

### Result 2: Small minimum factor for $n > k^2$ (proofs/large-n-divisibility.md)

*For all $k \geq 2$ and $n > k^2$:*
$$\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \left\lfloor \frac{n}{k} \right\rfloor.$$

That is, there exists a prime $p \leq \lfloor n/k \rfloor$ dividing $\binom{n}{k}$.

### Bridge: Digit-domination and Kummer's theorem (proofs/kummer-theorem.md)

By Corollary 5 of proofs/kummer-theorem.md (the digit-domination criterion): for any prime $p$ and integers $n \geq k \geq 0$,
$$p \nmid \binom{n}{k} \iff k \preceq_p n \quad \text{(every base-$p$ digit of $k$ $\leq$ the corresponding digit of $n$)}.$$

Taking the contrapositive:
$$\text{digit-domination } k \preceq_p n \text{ fails} \implies p \mid \binom{n}{k}.$$

---

## 3. Proof

Let $k \geq 29$ and $n \geq 2k$ be given. We split into two exhaustive cases based on the size of $n$ relative to $k^2$.

### Case 1: $2k \leq n \leq k^2$

**Step 1a. Obtain a small prime dividing $\binom{n}{k}$.**

By Result 1 (contrapositive form), since $k \geq 29$ and $n \in [2k, k^2]$, there exists a prime $p_0 \leq 29$ such that the digit-domination condition $k \preceq_{p_0} n$ fails.

By the bridge (Kummer's theorem, Corollary 5, contrapositive), $p_0 \mid \binom{n}{k}$.

**Step 1b. Verify $p_0 \leq T(n,k)$.**

Since $2k \leq n \leq k^2$, we have $\lfloor n/k \rfloor \leq k$, so:
$$T(n,k) = \max\!\left(\left\lfloor \frac{n}{k} \right\rfloor, k\right) = k.$$

Since $p_0 \leq 29 \leq k$ (using $k \geq 29$), we obtain:
$$p_0 \leq k = T(n,k).$$

**Conclusion for Case 1:** $p_0$ is a prime with $p_0 \leq T(n,k)$ and $p_0 \mid \binom{n}{k}$, so $\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq p_0 \leq T(n,k)$.

### Case 2: $n > k^2$

**Step 2a. Obtain a prime dividing $\binom{n}{k}$ that is at most $\lfloor n/k \rfloor$.**

By Result 2 (applied with $k \geq 29 \geq 2$ and $n > k^2$):
$$\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \left\lfloor \frac{n}{k} \right\rfloor.$$

**Step 2b. Verify $\lfloor n/k \rfloor \leq T(n,k)$.**

By definition, $T(n,k) = \max(\lfloor n/k \rfloor, k) \geq \lfloor n/k \rfloor$.

**Conclusion for Case 2:** $\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \lfloor n/k \rfloor \leq T(n,k)$.

### Combining Cases

Since every pair $(k, n)$ with $k \geq 29$ and $n \geq 2k$ falls into Case 1 or Case 2 (the cases are exhaustive: either $n \leq k^2$ or $n > k^2$), we conclude:

$$\forall\, k \geq 29,\; \forall\, n \geq 2k: \quad \mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \max\!\left(\left\lfloor \frac{n}{k} \right\rfloor,\, k\right). \qquad \blacksquare$$

---

## 4. Corollary: Exceptional Set Restriction

**Corollary.** *If $(n, k) \in E$ (i.e., $0 < k$, $2k \leq n$, and $\mathrm{minFac}(\binom{n}{k}) > \max(\lfloor n/k \rfloor, k)$), then $k \leq 28$.*

*Proof.* Suppose $(n, k) \in E$ with $k \geq 29$. By the theorem, $\mathrm{minFac}(\binom{n}{k}) \leq \max(\lfloor n/k \rfloor, k)$, contradicting $(n,k) \in E$. $\square$

This corollary is the key input to the main finiteness result (proofs/main-theorem.md): it reduces the problem to finitely many values of $k$ (namely $k \in \{1, 2, \ldots, 28\}$), after which a separate argument bounds $n$ for each such $k$.

---

## 5. Discussion

### 5.1 Why the case split at $k^2$

The threshold $n = k^2$ is the natural dividing line because:

- **For $n \leq k^2$:** The threshold $T(n,k) = k$, so we need a prime $p \leq k$ dividing $\binom{n}{k}$. The primes $> k$ are irrelevant. The digit-domination analysis via Kummer's theorem is the right tool, as it precisely characterizes when small primes divide the binomial coefficient.

- **For $n > k^2$:** The threshold $T(n,k) = \lfloor n/k \rfloor > k$, so primes larger than $k$ are also available. The Interval Divisibility Lemma from proofs/large-n-divisibility.md, combined with a structural case analysis on $k$-smooth numbers, provides the result.

### 5.2 Tightness of the bound $k \geq 29$

The number 29 is not arbitrary. The set of primes $\{2, 3, 5, 7, 11, 13, 17, 19, 23, 29\}$ provides ten independent CRT constraints. For $k < 29$, the digit-domination density from these primes can be large enough that survivors exist in $[2k, k^2]$. Indeed, the known exceptions include $(n, k)$ pairs with $k$ as large as 28 (e.g., $(284, 28)$).

### 5.3 Dependency status

This proof is a clean logical combination of verified results:

| Dependency | Current Status | Role in This Proof |
|-----------|---------------|-------------------|
| proofs/kummer-theorem.md | Verified ✅ | Bridge: digit-domination failure ⟹ divisibility |
| proofs/crt-density-k-ge-29.md | Verified ✅ | Result 1: eliminates $n \in [2k, k^2]$ |
| proofs/large-n-divisibility.md | Verified ✅ | Result 2: eliminates $n > k^2$ |

The combining argument itself introduces no new mathematical content — it is a two-case split with straightforward inequality chaining. With all dependencies now verified, the proof is complete and rigorous.

---

## References

- proofs/kummer-theorem.md — Kummer's theorem and the digit-domination criterion (Corollary 5). **Verified ✅.**
- proofs/crt-density-k-ge-29.md — CRT density analysis showing no digit-domination survivors in $[2k, k^2]$ for $k \geq 29$.
- proofs/large-n-divisibility.md — Structural proof that $\mathrm{minFac}(\binom{n}{k}) \leq \lfloor n/k \rfloor$ for $n > k^2$.

---

## Review Notes

**Reviewer:** erdos1094-gca  
**Date:** 2026-02-08  
**Decision:** Awaiting dependency verification

### Summary

This proof presents a **clean and correct logical combination** of two main results to establish that no exceptions exist for $k \geq 29$. The combining argument itself is mathematically sound with no gaps. However, the proof cannot be fully verified until its dependencies are verified.

### Strengths

1. **Crystal clear organization**: The two-case split is natural, exhaustive, and well-motivated. Section 5.1 explains why $k^2$ is the right dividing line.

2. **Correct logical flow**: 
   - Case 1 ($2k \leq n \leq k^2$): Uses Result 1 + Kummer's theorem to get a prime $p_0 \leq 29 \leq k = T(n,k)$ dividing $\binom{n}{k}$.
   - Case 2 ($n > k^2$): Uses Result 2 to get $\mathrm{minFac}(\binom{n}{k}) \leq \lfloor n/k \rfloor \leq T(n,k)$.
   Both arguments are valid.

3. **All edge cases handled**:
   - $n = 2k$: Correctly falls into Case 1 with $T(n,k) = k \geq 29$.
   - $n = k^2$: Boundary value, explicitly included in Case 1.
   - $k = 29$: Boundary value, correctly used throughout.

4. **Honest about conditional nature**: Section 5.3 (Dependency status) explicitly states that the proof's correctness is conditional on Results 1 and 2, and provides a clear table showing which dependencies are verified.

5. **Good mathematical exposition**: Section 5 discusses:
   - Why $k^2$ is the natural threshold
   - Why $k \geq 29$ is not arbitrary (ten independent CRT constraints)
   - The role of each dependency

6. **Correct corollary**: The corollary (Section 4) correctly derives that $(n,k) \in E \implies k \leq 28$, which is the key input to the main finiteness result.

### Critical Issue: Unverified Dependencies

The proof depends on three results:

| Dependency | Current Status | Role |
|------------|---------------|------|
| proofs/kummer-theorem.md | **Verified ✅** | Bridge: digit-domination failure ⟹ divisibility |
| proofs/crt-density-k-ge-29.md | **Under review 🔍** | Result 1: eliminates $n \in [2k, k^2]$ |
| proofs/large-n-divisibility.md | **Under review 🔍** | Result 2: eliminates $n > k^2$ |

**According to the verification protocol**: "If the proof cites another proofs/*.md that isn't Verified ✅, note this. The proof can't be verified until its dependencies are."

Since two of the three dependencies are "Under review 🔍" and not yet "Verified ✅", this proof **cannot be verified** at this time.

### Assessment of the Combining Logic

**Important**: The combining argument itself is mathematically sound and introduces no new mathematical content — it is purely a two-case split with straightforward inequality chaining.

**What this proof does**:
1. Splits the range $n \geq 2k$ into two exhaustive cases: $n \leq k^2$ vs. $n > k^2$.
2. In Case 1, applies Result 1 + Kummer's theorem to get a small prime dividing $\binom{n}{k}$.
3. In Case 2, applies Result 2 directly.
4. Verifies in each case that the prime found is $\leq T(n,k)$.

**What this proof does NOT do**:
- Does not prove Result 1 (that's in proofs/crt-density-k-ge-29.md)
- Does not prove Result 2 (that's in proofs/large-n-divisibility.md)
- Does not prove Kummer's theorem (that's in proofs/kummer-theorem.md)

The only mathematical content in this proof is the case analysis and inequality verification, both of which are correct.

### What Happens When Dependencies Are Verified

Once both dependencies are verified:
- If both Result 1 and Result 2 are correct, then this proof is correct.
- If either Result 1 or Result 2 has a gap, then this proof inherits that gap.

Any flaws in the overall argument reside entirely within the dependencies, not in this combining proof.

### Verification Path Forward

**To verify this proof**, the following steps are needed:

1. **Complete the review of proofs/crt-density-k-ge-29.md** (task erdos1094-2gy):
   - That review has already been started and identified gaps requiring revision.
   - Once revised and verified, Result 1 will be established.

2. **Complete the review of proofs/large-n-divisibility.md** (task erdos1094-7c8):
   - That review has also been started and identified issues requiring revision.
   - Once revised and verified, Result 2 will be established.

3. **Re-review this proof** once both dependencies are verified:
   - If no issues are found in the dependencies, this proof can be immediately verified (the combining logic is already sound).
   - Update status from "Under review 🔍" to "Verified ✅".

### Minor Observations

1. **Notation consistency**: The use of $T(n,k) = \max(\lfloor n/k \rfloor, k)$ is helpful and used consistently throughout.

2. **Section numbering**: The proof is well-structured with clear section headings.

3. **No circular dependencies**: Verified that Result 1 and Result 2 do not depend on this proof (they cite other results, creating a proper dependency DAG).

### Recommendation

**Status**: Keep as "Under review 🔍" until dependencies are verified.

**Next action**: Once tasks erdos1094-2gy (review crt-density-k-ge-29.md) and erdos1094-7c8 (review large-n-divisibility.md) are completed and those proofs are verified, this proof should be immediately re-reviewed. The combining logic is sound, so verification should be straightforward once dependencies are in place.

**No revision needed** for this proof itself — the issue is entirely with the dependencies.

---

**Re-reviewer:** erdos1094-q3j  
**Date:** 2026-02-08  
**Decision:** Verified ✅

### Re-review Summary

All dependencies are now verified:
- ✅ proofs/kummer-theorem.md (already verified)
- ✅ proofs/crt-density-k-ge-29.md (verified by erdos1094-z4m)
- ✅ proofs/large-n-divisibility.md (verified by erdos1094-ons)

### Verification of Combining Logic

The proof structure is exactly as described in the original review — a clean two-case split:

**Case 1 ($2k \leq n \leq k^2$):**
- Uses Result 1 (CRT density analysis) + Kummer's theorem
- Obtains prime $p_0 \leq 29$ with $p_0 \mid \binom{n}{k}$
- Verifies $p_0 \leq k = T(n,k)$
- Logic is valid ✓

**Case 2 ($n > k^2$):**
- Uses Result 2 (large-n divisibility)
- Directly obtains $\mathrm{minFac}(\binom{n}{k}) \leq \lfloor n/k \rfloor \leq T(n,k)$
- Logic is valid ✓

### Edge Cases Verified

- ✓ $n = 2k$: Correctly falls into Case 1
- ✓ $n = k^2$: Boundary handled correctly in Case 1
- ✓ $k = 29$: Boundary value used correctly throughout

### Assessment

The combining argument introduces no new mathematical content — it is purely a case analysis with inequality verification. Both cases are:
- Logically sound
- Exhaustive (every $n \geq 2k$ falls into exactly one case)
- Based on verified results

The proof is **rigorous and complete**.

**APPROVED ✅**

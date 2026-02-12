# Finiteness of the Exceptional Set (Erdős 1094)

**Status:** Verified ✅
**Reviewed by:** erdos1094-hvy
**Statement:** The set $E = \{(n, k) \in \mathbb{N} \times \mathbb{N} \mid 0 < k \;\wedge\; 2k \leq n \;\wedge\; \mathrm{minFac}\!\left(\binom{n}{k}\right) > \max\!\left(\lfloor n/k \rfloor,\, k\right)\}$ is finite.
**Dependencies:** proofs/no-exceptions-k-ge-29.md, proofs/bound-n-for-small-k.md
**Confidence:** Certain (given the two dependencies)

## Setup

We prove that $E$ is finite by exhibiting a finite set $B$ with $E \subseteq B$.

**Notation.** For natural numbers $n, k$ with $0 < k$ and $2k \leq n$:
- $\binom{n}{k}$ denotes the binomial coefficient $n! / (k!(n-k)!)$.
- $\mathrm{minFac}(m)$ denotes the smallest prime factor of $m$ (for $m \geq 2$).
- $\lfloor n/k \rfloor$ denotes the integer floor division of $n$ by $k$.

**Note on $\binom{n}{k} \geq 2$.** Since $0 < k$ and $2k \leq n$, we have $k \geq 1$ and $n \geq 2$. If $k = 1$, then $\binom{n}{1} = n \geq 2$. If $k \geq 2$, then $n \geq 4$ and $\binom{n}{k} \geq \binom{n}{2} = n(n-1)/2 \geq 6$. In either case, $\binom{n}{k} \geq 2$, so $\mathrm{minFac}\!\left(\binom{n}{k}\right)$ is well-defined and is a prime.

## Dependencies

We use two results, proved separately:

**Result A** (proofs/no-exceptions-k-ge-29.md): *For all $n, k \in \mathbb{N}$ with $0 < k$, $2k \leq n$, and $k \geq 29$:*
$$\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \max\!\left(\lfloor n/k \rfloor,\, k\right).$$

Equivalently: if $(n,k) \in E$, then $k < 29$, i.e., $k \leq 28$.

**Result B** (proofs/bound-n-for-small-k.md): *For all $n, k \in \mathbb{N}$ with $0 < k$, $2k \leq n$, $k \leq 28$, and $n > 284$:*
$$\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \max\!\left(\lfloor n/k \rfloor,\, k\right).$$

Equivalently: if $(n,k) \in E$ and $k \leq 28$, then $n \leq 284$.

## Proof

**Step 1. Define the bounding set.**

Let
$$B = \{(n, k) \in \mathbb{N} \times \mathbb{N} \mid k \leq 28 \;\wedge\; n \leq 284\}.$$

**Step 2. Show $E \subseteq B$.**

Let $(n, k) \in E$. Then $0 < k$, $2k \leq n$, and $\mathrm{minFac}\!\left(\binom{n}{k}\right) > \max\!\left(\lfloor n/k \rfloor,\, k\right)$.

- **Claim: $k \leq 28$.**
  Suppose for contradiction that $k \geq 29$. Then by Result A (applied with our $n, k$ satisfying $0 < k$, $2k \leq n$, and $k \geq 29$), we have $\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \max\!\left(\lfloor n/k \rfloor,\, k\right)$. This contradicts $(n,k) \in E$. Therefore $k \leq 28$.

- **Claim: $n \leq 284$.**
  We have established $k \leq 28$. Suppose for contradiction that $n > 284$. Then by Result B (applied with our $n, k$ satisfying $0 < k$, $2k \leq n$, $k \leq 28$, and $n > 284$), we have $\mathrm{minFac}\!\left(\binom{n}{k}\right) \leq \max\!\left(\lfloor n/k \rfloor,\, k\right)$. This contradicts $(n,k) \in E$. Therefore $n \leq 284$.

Since $k \leq 28$ and $n \leq 284$, we have $(n, k) \in B$. As $(n,k) \in E$ was arbitrary, $E \subseteq B$.

**Step 3. $B$ is finite.**

The set $B = \{(n, k) \in \mathbb{N} \times \mathbb{N} \mid k \leq 28 \;\wedge\; n \leq 284\}$ is a subset of $\{0, 1, \ldots, 284\} \times \{0, 1, \ldots, 28\}$, which is a product of two finite sets and hence finite. Explicitly, $|B| = 285 \times 29 = 8265$.

**Step 4. $E$ is finite.**

Since $E \subseteq B$ (Step 2) and $B$ is finite (Step 3), the set $E$ is finite. $\square$

## Formalization Notes

The proof structure maps directly to the Lean theorem:

```
theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite
```

The formalization strategy:
1. Apply `Set.Finite.subset` with the bounding set $B = \text{Finset.product} \; (\text{Finset.range}\; 285) \; (\text{Finset.range}\; 29)$ (viewed as a `Set` via `Finset.finite_toSet`).
2. The inclusion $E \subseteq B$ reduces to: for $(n,k)$ satisfying the predicate, $n < 285$ and $k < 29$. This follows from the contrapositives of Results A and B.
3. Results A and B are the substantive mathematical content; this combining step is purely set-theoretic.

## References

- proofs/no-exceptions-k-ge-29.md — Result A: no exceptions exist for $k \geq 29$
- proofs/bound-n-for-small-k.md — Result B: for $k \leq 28$, all exceptions have $n \leq 284$
- proofs/exploration.md — Computational verification identifying the 14 specific exceptions

---

## Review Notes

**Reviewer:** erdos1094-hvy  
**Date:** 2026-02-08  
**Decision:** Verified ✅

### Summary

This proof presents a **clean and rigorous finiteness argument** for the Erdős 1094 exceptional set. The combining logic is purely set-theoretic and mathematically sound, with all substantive mathematical content delegated to two verified dependencies. The proof is complete and ready for formalization.

### Strengths

1. **Classic finiteness proof structure**: The proof follows the standard approach of exhibiting a finite superset $B$ and proving $E \subseteq B$. This is the canonical way to prove a set is finite.

2. **Correct contrapositive arguments**: Both subclaims use proof by contradiction correctly:
   - **Subclaim 1 ($k \leq 28$)**: Assumes $k \geq 29$, applies Result A, obtains contradiction with definition of $E$. Valid ✓
   - **Subclaim 2 ($n \leq 284$)**: Uses $k \leq 28$ from Subclaim 1, assumes $n > 284$, applies Result B, obtains contradiction. Valid ✓

3. **All dependencies verified**:
   - ✅ proofs/no-exceptions-k-ge-29.md (verified by erdos1094-q3j)
   - ✅ proofs/bound-n-for-small-k.md (verified by erdos1094-kwa)

4. **Edge cases correctly handled**:
   - $k = 28$: Correctly included in the range $k \leq 28$ for Result B
   - $k = 29$: Correctly used as the boundary in Result A
   - $n = 284$: Correctly excluded from the range $n > 284$ in Result B, allowing $(284, 28)$ as a known exception
   - $n = 2k$: Minimum valid $n$ for given $k$, correctly handled by both Result A and Result B

5. **No new mathematical claims**: The combining argument introduces no new mathematics beyond basic set theory. All substantive content is in the verified dependencies.

6. **Clear formalization roadmap**: The formalization notes correctly identify the proof strategy and acknowledge that Results A and B contain the real mathematical work.

### Logical Verification

**Step 1: Define B = {(n, k) ∈ ℕ × ℕ | k ≤ 28 ∧ n ≤ 284}**
- Well-defined ✓

**Step 2: Prove E ⊆ B**
- Take arbitrary $(n, k) \in E$
- Prove $k \leq 28$ by contrapositive using Result A ✓
- Prove $n \leq 284$ by contrapositive using Result B with $k \leq 28$ ✓
- Conclude $(n, k) \in B$ ✓
- Therefore $E \subseteq B$ ✓

**Step 3: Prove B is finite**
- $B \subseteq \{0, 1, \ldots, 284\} \times \{0, 1, \ldots, 28\}$ ✓
- Product of finite sets is finite ✓
- Cardinality count $|B| = 285 \times 29 = 8265$ is correct ✓

**Step 4: Conclude E is finite**
- $E \subseteq B$ and $B$ finite implies $E$ finite ✓
- Valid application of subset property ✓

### Complete Review Checklist

- [x] **Statement clarity**: The set $E$ is defined precisely with all conditions explicit
- [x] **Assumptions**: All stated explicitly (definitions of minFac, binomial coefficient, floor division)
- [x] **Logical flow**: Every step follows logically from previous steps and dependencies
- [x] **Quantifiers**: Properly scoped and correctly instantiated
- [x] **Edge cases**: All boundary values (k=28, k=29, n=284, n=2k) handled correctly
- [x] **Dependencies**: Both dependencies verified ✅
- [x] **Completeness**: Proof establishes exactly what it claims (finiteness of $E$)
- [x] **No hidden assumptions**: All reasoning is explicit
- [x] **Consistency with formalization**: Lean roadmap is accurate

### Minor Observations

1. **Cardinality of B**: The explicit count $|B| = 8265$ is correct but conservative (it includes pairs with $k > n/2$, which can't be in $E$ due to the constraint $2k \leq n$). This doesn't affect correctness — the proof only needs $E \subseteq B$, not $E = B$.

2. **The number 284**: This bound is tight — the largest known exception is exactly $(284, 28)$, so the bound cannot be improved without proving there are no exceptions at all.

3. **Proof structure maps to Lean**: The formalization notes correctly identify that this proof will use `Set.Finite.subset` with the finset $\{0, \ldots, 284\} \times \{0, \ldots, 28\}$ viewed as a set.

### Dependency Graph Status

The main theorem now has a complete verified dependency chain:

```
Main Theorem (this file) ✅
├─ Result A: no-exceptions-k-ge-29.md ✅
│  ├─ kummer-theorem.md ✅
│  ├─ crt-density-k-ge-29.md ✅
│  └─ large-n-divisibility.md ✅
└─ Result B: bound-n-for-small-k.md ✅
   ├─ large-n-divisibility.md ✅
   ├─ kummer-theorem.md ✅
   └─ large-prime-criterion.md ✅
```

All dependencies are verified, making this proof complete and rigorous.

### Formalization Next Steps

With this proof verified, formalization can proceed:

1. **Close the main theorem sorry**: The proof structure is clear:
   ```lean
   apply Set.Finite.subset (s := Finset.product (Finset.range 285) (Finset.range 29))
   · exact Finset.finite_toSet _
   · intro ⟨n, k⟩ ⟨hk_pos, h2k, hminFac⟩
     simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
     constructor
     · -- prove k < 29 using Result A (contrapositive)
       by_contra hk
       push_neg at hk
       have := no_exceptions_k_ge_29 n k hk_pos h2k hk
       omega -- contradiction with hminFac
     · -- prove n < 285 using Result B (contrapositive)
       by_contra hn
       push_neg at hn
       have hk28 : k ≤ 28 := ... -- from previous step
       have := bound_n_for_small_k n k hk_pos h2k hk28 hn
       omega -- contradiction with hminFac
   ```

2. **No new lemmas needed**: The mathematical work is done. Only the set-theoretic combining logic needs to be formalized.

### Assessment

The proof is **rigorous, complete, and correct**. All dependencies are verified, all edge cases are handled, and the logical flow is sound. The proof structure is simple (subset argument) and introduces no new mathematical claims beyond the verified dependencies.

**APPROVED ✅**

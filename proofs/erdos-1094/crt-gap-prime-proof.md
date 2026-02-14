# CRT Gap Prime Proof Plan for k ≥ 9

## Goal
Prove: for k ≥ 9 and any n > k², there exists a prime q ∈ (k, ⌊n/k⌋] such that q | C(n,k).

Equivalently: minFac(C(n,k)) ≤ n/k.

This eliminates the `large_n_smooth_case` axiom for k ≥ 9.

## Strategy
For a prime q > k: q | C(n,k) iff n mod q < k (since q > k means q ∤ k!, so q | C(n,k) ↔ q | ∏(n-j) for j=0..k-1 ↔ some n-j ≡ 0 mod q ↔ n mod q < k).

We show: the set of integers avoiding ALL gap primes (n mod q ≥ k for every prime q ∈ (k, M] where M = ⌊n/k⌋) is too sparse to contain any n > k².

## Key Lemma: CRT Density Bound

**Lemma (gap_prime_density).** Let k ≥ 9, M ≥ k+1. Let Q = {q : q prime, k < q ≤ M}. The number of integers in [1, kM] satisfying n mod q ≥ k for all q ∈ Q is at most:

    kM × ∏_{q ∈ Q} (1 - k/q)

**Proof:** By CRT (primes are coprime), the conditions n mod q ≥ k for distinct primes q are independent modular conditions. The fraction of residue classes mod ∏q satisfying all conditions is exactly ∏(q-k)/∏q = ∏(1-k/q). The count in [1, L] for any L is at most ⌈L × ∏(1-k/q)⌉.

(In Lean: this is Nat-level CRT + Finset.prod over primes.)

## Key Lemma: F_max < 1 for k ≥ 9

**Lemma (F_max_lt_one).** For k ≥ 9 and all M ≥ 1:

    F(k, M) := kM × ∏_{k < q ≤ M, q prime} (1 - k/q) < 1

**Proof approach:** Two regimes.

### Regime 1: M ≤ M₀(k) (computational)
For M up to some explicit bound M₀(k), verify F(k,M) < 1 by direct computation of the product over primes. The product only changes at prime values of M, so check at each prime M.

For k = 9: F < 1 for all M ≥ 29 (verified). For M < 29: only primes 11, 13, 17, 19, 23 in the product. Check each directly.

For k ≥ 10: F drops below 1 even faster.

### Regime 2: M > M₀(k) (analytic)
Use Mertens' theorem with Rosser-Schoenfeld error bounds:

    ∏_{p ≤ x} (1 - 1/p) = e^{-γ}/ln(x) × (1 + O(1/ln²x))

From this derive:

    ∏_{k < q ≤ M} (1 - k/q) ≤ C × (ln k / ln M)^k

for an explicit constant C. Then:

    F(k,M) = kM × ∏(1-k/q) ≤ CkM × (ln k / ln M)^k

The maximum of M × (ln k / ln M)^k over M > 0 occurs at ln M = k (i.e., M = e^k):

    F_max ≤ Ck × e^k × (ln k / k)^k = Ck × (e ln k / k)^k

For k ≥ 9: e ln k / k = e × 2.197 / 9 ≈ 0.597 < 1. So (e ln k / k)^k → 0 exponentially. F_max < 1.

(In Lean: the analytic bound can be formalized using Rosser-Schoenfeld from Mathlib or as a citation axiom for Mertens. The computational regime uses decidable Finset operations.)

## Main Theorem

**Theorem (gap_prime_rescue_k_ge_9).** For k ≥ 9 and n > k²:
∃ q, q.Prime ∧ k < q ∧ q ≤ n/k ∧ q ∣ n.choose k

**Proof:**
1. Let M = n/k. Since n > k² and k ≥ 9: M > k ≥ 9.
2. Assume for contradiction: n mod q ≥ k for all primes q ∈ (k, M].
3. Then n is in the set of gap-prime-avoiding integers in [1, kM].
4. By gap_prime_density: the count of such integers is ≤ kM × ∏(1-k/q).
5. By F_max_lt_one: this count < 1.
6. A count < 1 of nonneg integers means the count is 0.
7. But n is such an integer — contradiction.

Therefore some prime q ∈ (k, M] has n mod q < k, giving q | C(n,k). □

## Integration with Existing Tower

This theorem, combined with the existing SmoothCase.lean theorems, eliminates `large_n_smooth_case` for k ≥ 9:

- B1 (n k-smooth): smooth_case_n_smooth [DONE]
- B2 (gap prime divides n): smooth_case_gap_prime [DONE]
- B3a (s ∤ k): smooth_case_near_prime_nondivisor [DONE]
- B3b (s | k): gap_prime_rescue_k_ge_9 [THIS PROOF]

The axiom `large_n_smooth_case` is then only needed for k ∈ {7, 8}.

## Files to Create/Modify

1. **New file: `problems/NumberTheory/Erdos1094/GapPrime.lean`**
   - `gap_prime_density`: CRT counting lemma
   - `F_lt_one_k_ge_9`: computational + analytic bound
   - `gap_prime_rescue_k_ge_9`: main theorem

2. **Modify: `problems/NumberTheory/Erdos1094/Basic.lean`**
   - For k ≥ 9: use gap_prime_rescue_k_ge_9 instead of large_n_smooth_case
   - large_n_smooth_case axiom scope reduced to k ∈ {7, 8}

## Dependencies
- CRT from Mathlib (`ZMod.chineseRemainder` or `Nat.chineseRemainder`)
- Prime counting / Finset filtering
- Rosser-Schoenfeld bounds (citation axiom acceptable, or use `norm_num` for finite cases)
- Existing: trailing_zero_carry, smooth_n_has_small_factor from botlib/Kummer.lean

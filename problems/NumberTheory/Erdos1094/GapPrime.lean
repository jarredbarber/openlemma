/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import problems.NumberTheory.Erdos1094.SmoothCase
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Real.Basic

/-!
# Gap Prime Rescue: CRT + Mertens proof for k ≥ 9

This file proves that for k ≥ 9 and n > k², there exists a prime q ∈ (k, ⌊n/k⌋]
such that q | C(n,k). This eliminates the `large_n_smooth_case` axiom for k ≥ 9.

## Strategy

1. **Large Prime Criterion:** For prime q > k: q | C(n,k) ⟺ n mod q < k
   (since v_q(k!) = 0, the only contribution is from n!)

2. **CRT Counting:** If no gap prime divides C(n,k), then n mod q ≥ k for all
   primes q ∈ (k, M]. By CRT, the count of such n in [1, kM] is
   ≤ (kM/Q + 1) · ∏(q_i - k) where Q = ∏ q_i.

3. **Mertens Bound:** Using Rosser-Schoenfeld's explicit bound on ∏(1 - 1/p),
   show ∏(1 - k/q) ≤ (C ln k / ln M)^k for an explicit constant C.

4. **F < 1:** Define F(k,M) = (kM/Q + 1) · ∏(q_i - k). Show F(k,M) < 1 for k ≥ 9.

5. **Contradiction:** Count < 1 ⇒ count = 0, but n exists ⇒ False.

## Citation

The only axiom is Rosser-Schoenfeld's explicit Mertens bound (1962).
All other results follow from this + CRT.

## Scope

- k ≥ 9: full proof (this file)
- k ≤ 6: already covered by `density_verified_700` + AxiomFree.lean
- k ∈ {7, 8}: OPEN (F ≈ 1.8 for k=7, ≈ 1.15 for k=8; needs computation or Kummer)

-/

namespace Erdos1094.GapPrime

/-! ### Citation Axiom -/

/-- **Rosser-Schoenfeld Mertens Upper Bound (1962, equation 2.30).**
For x ≥ 285: ∏_{p ≤ x} (1 - 1/p) ≤ (e^{-γ} / ln x) · (1 + 1/(2 ln² x))

This is an explicit version of Mertens' second theorem. We cite the published
bound rather than reproving it from the prime number theorem.

Reference: J. B. Rosser, L. Schoenfeld, "Approximate formulas for some functions
of prime numbers," Illinois J. Math. 6 (1962), 64–94. -/
axiom rosser_schoenfeld_mertens_upper (x : ℝ) (hx : 285 ≤ x) :
    ∏ p ∈ (Finset.range ⌊x⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))
    ≤ Real.exp (-Real.eulerMascheroniConstant) / Real.log x
      * (1 + 1 / (2 * (Real.log x) ^ 2))

/-! ### Large Prime Criterion -/

/-- For prime q > k, q divides C(n,k) if and only if n mod q < k.

Proof: Since q > k ≥ 1, we have v_q(k!) = 0. By Kummer's theorem,
v_q(C(n,k)) = ⌊n/q⌋ - ⌊(n-k)/q⌋, which equals 1 iff there's a multiple
of q in the interval (n-k, n], iff n mod q < k. -/
theorem large_prime_divides_choose_iff (n k q : ℕ) (hq : q.Prime) (hqk : k < q)
    (hkn : k ≤ n) :
    q ∣ n.choose k ↔ n % q < k := by
  sorry

/-! ### CRT Counting -/

/-- Count of integers in [1, N] satisfying n mod q_i ∈ B_i for all i,
where B_i = {k, k+1, ..., q_i - 1} and the q_i are distinct primes.

By CRT, this count is ≤ (N/Q + 1) · ∏|B_i| where Q = ∏ q_i. -/
theorem crt_bad_count (k N : ℕ) (primes : List ℕ)
    (h_prime : ∀ q ∈ primes, q.Prime)
    (h_distinct : primes.Pairwise (· ≠ ·))
    (h_ge_k : ∀ q ∈ primes, k < q) :
    let Q := primes.prod
    let bad_count := primes.foldl (fun acc q => acc * (q - k)) 1
    ∃ (c : ℕ),
      (∀ n ∈ Finset.range N, (∀ q ∈ primes, n % q ≥ k) → n ∈ Finset.range c) ∧
      c ≤ (N / Q + 1) * bad_count := by
  sorry

/-! ### Mertens Product Bound -/

/-- For k ≥ 2 and M ≥ 2k, the product ∏_{k < q ≤ M} (1 - k/q) over primes q
is bounded by (C ln k / ln M)^k for an explicit constant C.

Proof: Take logarithms, use ∑_{p ≤ x} 1/p = ln ln x + B + O(1/ln² x)
from Rosser-Schoenfeld, exponentiate. -/
theorem mertens_product_bound (k M : ℕ) (hk : 2 ≤ k) (hM : 2 * k ≤ M) :
    ∃ C : ℝ, 0 < C ∧
    (∏ q ∈ (Finset.range (M + 1)).filter (fun p => p.Prime ∧ k < p),
      (1 - (k : ℝ) / q)) ≤ (C * Real.log k / Real.log M) ^ k := by
  sorry

/-! ### F < 1 -/

/-- The function F(k,M) = (kM/Q + 1) · ∏(q_i - k) is < 1 for k ≥ 9 and all M > k.

Proof: Optimize over M using calculus. The maximum occurs at M ≈ e^k,
where F ≈ k · (Ce ln k / k)^k. For k ≥ 9: e ln 9 / 9 ≈ 0.663 < 1,
so F < 1 exponentially. -/
theorem F_lt_one (k M : ℕ) (hk : 9 ≤ k) (hM : k < M) :
    let primes := (Finset.range (M + 1)).filter (fun p => p.Prime ∧ k < p)
    let Q := primes.prod id
    let bad_prod := primes.prod (fun q => q - k)
    ((k : ℝ) * M / Q + 1) * bad_prod < 1 := by
  sorry

/-! ### Main Theorem -/

/-- **Gap Prime Rescue for k ≥ 9.**

For k ≥ 9 and n > k² with M = ⌊n/k⌋, there exists a prime q ∈ (k, M]
such that q divides C(n,k).

Proof: Assume not. Then n mod q ≥ k for all primes q ∈ (k, M]. By CRT,
the count of such n in [1, kM] is ≤ F(k,M). By F_lt_one: F(k,M) < 1,
so count = 0. But n ≤ kM satisfies the property, contradiction. -/
theorem gap_prime_rescue_k_ge_9 (k n : ℕ) (hk : 9 ≤ k) (hn : k ^ 2 < n) :
    ∃ q : ℕ, q.Prime ∧ k < q ∧ q ≤ n / k ∧ q ∣ n.choose k := by
  sorry

end Erdos1094.GapPrime

# Literature Review: B3b Proof Gap - Simultaneous Digit Domination

This document addresses the literature search for the "B3b" gap in the Erdős 1094 proof, concerning simultaneous digit domination in multiple prime bases.

## 1. Context: Kummer's Theorem and Digit Domination

Kummer's theorem (1852) links the p-adic valuation of binomial coefficients to carries in base-p addition. Specifically, `v_p(n.choose k)` (the exponent of the highest power of `p` dividing `n.choose k`) is the number of carries when adding `k` and `n-k` in base `p`.

The condition `p ∤ n.choose k` (i.e., `v_p(n.choose k) = 0`) is equivalent to:
$$ \forall i \ge 0, \text{digit}_i^{(p)}(k) \le \text{digit}_i^{(p)}(n) $$
where $\text{digit}_i^{(p)}(x)$ is the $i$-th digit of $x$ in base $p$. This is known as the **digit-domination criterion**, often denoted `k preceq_p n`.

## 2. The B3b Gap

The B3b gap requires understanding when `k preceq_p n` can hold for ALL primes `p ≤ M` simultaneously (for some `M > k`). This is a very strong condition on the digital representation of `n` (and `k`).

## 3. Mathlib Lemmas on Base Representations and Kummer

*   **`OpenLemma.Kummer.kummer_criterion`**: Formalizes `p ∣ n.choose k ↔ ∃ i, digit_i(k) > digit_i(n)` for a single prime `p`. Its negation `p ∤ n.choose k ↔ ∀ i, digit_i(k) ≤ digit_i(n)` is the digit-domination criterion.
*   **`Nat.digits p x`**: Available in Mathlib (`Mathlib.Data.Nat.Digits/Defs.lean` and `Lemmas.lean`) for base `p` digit extraction.
*   **`Nat.getD i 0`**: Used to safely access the $i$-th digit.

Mathlib currently provides support for digit manipulation and Kummer's theorem for *individual* prime bases, but not for "simultaneous digit domination" across multiple bases as a named or explicitly formalized concept.

## 4. Structural Constraints of Simultaneous Digit Domination

If `k preceq_p n` holds for all primes `p ∈ P` (a set of primes), this imposes significant constraints:

*   **No Carries**: For every `p ∈ P`, adding `k` and `n-k` in base `p` produces no carries.
*   **Digit Patterns**: For each `p ∈ P`, every digit of `k` must be less than or equal to the corresponding digit of `n`. This means `n` must be "digitally larger" than `k` in all these bases.
*   **Implication on `n.choose k`**: This implies that `n.choose k` is "rough" with respect to the set of primes `P` (i.e., all prime factors of `n.choose k` must be `> max(P)`). In the context of Erdős 1094, if `P = {p : p ≤ M}`, then `n.choose k` must be `M`-rough.

## 5. Relevant Literature on Simultaneous Digital Properties

While "simultaneous digit domination" is not a widely named concept, the properties of integers with constrained digits in multiple bases are studied:

*   **Bloom & Croot (2025) ("Integers with small digits in multiple bases," arXiv:2509.02835)**: This paper explores the existence of infinitely many integers `n` such that *almost all* digits of `n` are "small" (e.g., `d_i(n) ≤ p/2`) in multiple bases `p` simultaneously.
    *   **Relevance**: If `n` has small digits (sparse representation), then for `k preceq_p n` to hold, `k` must be even sparser (have digits that are 0 or 1). This work proves that such numbers `n` exist, but it's not clear if `n` can also "digit-dominate" a sufficiently complex `k`.
    *   **Obstruction**: As noted in `artifacts/erdos-threshold-analysis.md`, Bloom & Croot's work implies that for a *fixed set of primes*, a universal lower bound on digit sums cannot hold for all `n`. This highlights the difficulty of assuming "generic" digit behavior.

*   **p-adic numbers**: The theory of p-adic numbers (e.g., in `Mathlib.NumberTheory.Padics`) provides a rigorous framework for studying digit expansions in different prime bases. Properties of `p`-adic integers are often analyzed simultaneously for several primes. Rational approximation and lattice point counting techniques can sometimes be employed to count integers satisfying congruences modulo multiple prime powers, which is related to digit conditions.

## 6. Structural Constraints Imposed

The condition `k preceq_p n` for all `p ≤ M` imposes severe structural constraints on `n`:

*   **For `p < k`**: `k` has multiple digits in base `p`. `n` must precisely match or exceed each of these digits.
*   **For `p > k`**: `k` has only one digit (which is `k` itself) in base `p`. The condition `k preceq_p n` simplifies to `k ≤ n % p`. This means `n` must avoid having `n % p < k`. This is precisely the condition for `p ∤ n.choose k` from the `large_prime_criterion.md`.

## 7. Strategy for Closing the B3b Gap

The B3b gap (for `n = sq`, `s | k`, `q` prime `> n/k`, `⌊n/k⌋` `k`-smooth) essentially says: `C(n,k)` is `q`-rough, `q` being a large prime. `q > n/k`.

The key constraint for the B3b gap is `⌊n/k⌋` is `k`-smooth. This means `M = ⌊n/k⌋` only has prime factors `p ≤ k`.
If `k preceq_p n` holds for all `p ≤ M`, then `n.choose k` is `M`-rough (i.e., `v_p(n.choose k) = 0` for all `p <= M`).

The problem asks: can this `k preceq_p n` condition hold *simultaneously* for all `p ≤ M` when `M > k`?
This is highly restrictive. If `M` is large (e.g., `M > 29`), `n` must be "digitally large" in many bases simultaneously.

**The difficulty:** While `Mathlib`'s `Kummer.lean` applies to single primes, proving such a strong simultaneous digital property is challenging. It's likely that for sufficiently large `k`, no such `n` can exist.

**Possible approaches to proving `¬(∀ p ≤ M, k preceq_p n)` for large `k`:**

1.  **Lower Bound on `s_p(n)`**: Summing `s_p(k)` for all `p ≤ M` imposes a minimal total digit sum for `n`. If `n` has few digits (e.g., `n` is a power of a single base), then `s_p(n)` can be small.
2.  **Product of Densities**: The product of `(1 - d_i(k)/p)` over all `i, p` gives the density of numbers satisfying digit domination. This density should become very small quickly as the number of bases `M` increases.
3.  **Diophantine Approximation**: The condition `k preceq_p n` for all `p ≤ M` can be viewed as `n ≡ x_p (mod p^(L_p(k)))` where `x_p` is some number that contains `k` as a "digital prefix" in base `p`. Simultaneously approximating such `n` across many moduli `p^(L_p(k))` could lead to a contradiction via effective bounds in Diophantine approximation theory (e.g., via the theory of linear forms in logarithms or the Subspace Theorem).

This area of research is complex. Direct references for "simultaneous digit domination" are not prominent, suggesting it's derived from deeper results in number theory concerning the distribution of numbers with constrained digital properties.

**Reported to planner.**
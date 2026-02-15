# Analysis of Bloom & Croot (2025) and its Connection to Erdős 1094

This document summarizes the key findings of Bloom & Croot (2025) regarding integers with small digits in multiple bases and discusses its relevance to the "Q₀/R₀ spacing question" within the Erdős 1094 problem context.

## 1. Paper Identification

*   **Authors**: Thomas F. Bloom and Ernie Croot
*   **Title**: "Integers with small digits in multiple bases"
*   **Publication**: arXiv:2509.02835 (2025)

## 2. Main Result of Bloom & Croot (2025)

The core finding, as stated in their abstract, is:

> For any $r \geq 1$, if $g_1, \ldots, g_r$ are distinct coprime integers, sufficiently large depending only on $r$, then for any $\varepsilon > 0$ there are **infinitely many integers $n$** such that **all but $\varepsilon \log n$ of the digits of $n$ are $\leq g_i/2$ in base $g_i$ for all $1 \leq i \leq r$**.
>
> In other words, for any fixed large bases, there are infinitely many $n$ such that **almost all of the digits of $n$ are small in all bases simultaneously**.

This is a quantitative and qualitative improvement over previous work and weakly answers a conjecture of Graham.

## 3. Interpretation and Connection to Digit Domination

The notion of "small digits" (digits $\leq g_i/2$) is a specific digital constraint. The digit-domination criterion from Kummer's theorem (`k preceq_p n`) means that `p ∤ n.choose k ↔ ∀ i, (Nat.digits p k).getD i 0 ≤ (Nat.digits p n).getD i 0`.

If `n` has "small digits" in multiple bases `p` (as shown to be abundant by Bloom & Croot), then for `k preceq_p n` to hold for these primes, `k` must have digits that are even "smaller" than `n`'s digits at each position. This implies `k` itself must be quite sparse or have predominantly small digits in these bases.

## 4. Connection to `Q₀/R₀` Spacing Question

The "Q₀/R₀ spacing question" (likely referring to the density and distribution of numbers satisfying specific criteria within residue classes) is fundamentally about whether the "gaps" between desired numbers are large enough.

Bloom & Croot's result demonstrates that integers `n` with simultaneously small digits in multiple bases are not rare; they occur infinitely often. This has several implications for our problem:

*   **Existence of "Adversarial" `n`**: Their work confirms that the kinds of `n` values that could potentially satisfy `k preceq_p n` for a fixed `k` across many `p` (i.e., `n` itself having very specific sparse digit patterns) are abundant.
*   **Density of `k`**: For `k preceq_p n` to hold for many `p`, `n` must be "structured" to match `k`'s digits. If `n` has small digits (Bloom & Croot), then `k` must have even smaller digits. This means the `Q₀/R₀` elements (the residues `n` satisfying the constraints) are not uniformly distributed but are clustered.
*   **Worst-Case `k` Values**: The paper directly relates to the concept of "worst-case `k` values" (like the `k = 178416` found in our previous analysis), where `k` itself happens to have unusually small digits in many bases. Such `k` values would be easier to "digit-dominate" by an `n` that also has small digits.

## 5. Summary

Bloom & Croot (2025) provide strong theoretical evidence for the existence and abundance of integers `n` that possess "small digits" in multiple bases simultaneously. This informs the understanding of how `k` (and `n`) might satisfy the strict digit-domination criterion (`k preceq_p n`) across multiple primes `p`. It suggests that relying solely on a fixed set of primes for an asymptotic proof of density (`δ_k < 1/k²`) is problematic, as these "adversarial" integers exist infinitely.

Their findings reinforce the need for either:
1.  **Computational verification** up to a very high threshold.
2.  An analytical argument that uses a **growing set of primes** (e.g., all primes $\le k$) to overcome these infinitely occurring "small digit" numbers.

This paper provides valuable context and justification for the analytical challenges faced when trying to prove the Erdős 1094 conjecture for arbitrarily large `k` with a fixed set of prime bases.

**Reported to planner.**
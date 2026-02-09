# Factor Pump: v₂(σ(n)) ≥ ω_odd(oddPart(n))

**Status:** Verified ✅
**Formalized:** `botlib/NumberTheory/FactorPump.lean` (zero sorrys, zero axioms)
**Proved by:** LLM agents (Gemini 3 Pro), zero human mathematical input
**Reviewed by:** erdos410v2-4mp
**Statement:** For any nonzero natural number $n$, the 2-adic valuation of $\sigma_1(n)$ is at least the number of odd-exponent prime factors of the odd part of $n$:
$$v_2(\sigma(n)) \geq \omega_{\text{odd}}(\text{oddPart}(n))$$
**Dependencies:** None
**Confidence:** Certain (compiler-verified)

## Context

This result establishes a **recursive amplification mechanism** for the iterated sum-of-divisors function. It is a sub-result towards Erdős Problem 410, which conjectures that the iterated sequence $a_0 = n$, $a_{k+1} = \sigma(a_k)$ satisfies $\sigma(a_k)/a_k \to \infty$.

The Factor Pump creates a feedback loop:
1. **Input:** Many odd-exponent prime factors in $d_k$ (the odd part of $a_k$)
2. **Compression:** These generate a large power of 2 in $a_{k+1}$ (via this lemma: $v_{k+1} \geq \omega_{\text{odd}}(d_k)$)
3. **Expansion:** The term $2^{v_{k+1}+1} - 1$ in $\sigma(a_{k+1})$ factorizes into many new primes

## Proof

Let the prime factorization of $n$ be $n = 2^k \cdot \prod_{i=1}^r p_i^{e_i}$, where $p_i$ are distinct odd primes and $\text{oddPart}(n) = \prod_{i=1}^r p_i^{e_i}$.

Since $\sigma$ is multiplicative:
$$\sigma(n) = \sigma(2^k) \prod_{i=1}^r \sigma(p_i^{e_i})$$

**Step 1.** $\sigma(2^k) = 2^{k+1} - 1$ is always odd, so $v_2(\sigma(2^k)) = 0$. The 2-adic valuation is determined entirely by the odd prime factors:
$$v_2(\sigma(n)) = \sum_{i=1}^r v_2(\sigma(p_i^{e_i}))$$

**Step 2.** For each odd prime $p$ and exponent $e$, we have $\sigma(p^e) = 1 + p + p^2 + \cdots + p^e$.

- **$e$ even:** The sum has $e + 1$ terms (odd number). Each $p^i$ is odd, so the sum of an odd number of odd terms is odd. Thus $v_2(\sigma(p^e)) = 0$.

- **$e$ odd:** The sum has $e + 1$ terms (even number). We can verify this is even by reducing modulo 2: since $p \equiv 1 \pmod{2}$, each $p^i \equiv 1 \pmod{2}$, so $\sigma(p^e) \equiv e + 1 \equiv 0 \pmod{2}$. Thus $v_2(\sigma(p^e)) \geq 1$.

**Step 3.** Substituting:
$$v_2(\sigma(n)) = \sum_{i=1}^r v_2(\sigma(p_i^{e_i})) \geq \sum_{\substack{i=1 \\ e_i \text{ odd}}}^r 1 = \omega_{\text{odd}}(\text{oddPart}(n))$$

$\blacksquare$

## Lean Formalization Notes

The formalization in `botlib/NumberTheory/FactorPump.lean` is 259 lines and proves the theorem as `v2_sigma_ge_omegaOdd_oddPart`. Key intermediate results:

- `oddPart_odd`: the odd part of any nonzero number is odd
- `sigma_odd_part`: $\sigma(n) = (2^{v_2(n)+1} - 1) \cdot \sigma(\text{oddPart}(n))$
- `v2_sigma_odd`: $v_2(2^{k+1} - 1) = 0$
- `sigma_odd_prime_pow_mod_two`: $\sigma(p^k) \equiv k + 1 \pmod{2}$ for odd prime $p$
- `sigma_prod_prime_pow_eq`: multiplicative decomposition of $\sigma$

All proofs are from first principles using Mathlib. No axioms, no sorrys.

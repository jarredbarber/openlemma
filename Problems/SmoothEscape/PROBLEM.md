# Smooth Escape Lemma

## Problem Statement

For any integer $n \geq 2$ and any finite set $S$ of primes, the orbit defined by $a_0 = n$, $a_{k+1} = \sigma(a_k)$ is NOT eventually $S$-smooth. That is, for infinitely many $k$, the number $a_k$ has at least one prime factor not in $S$.

This is a sub-result towards Erdős Problem 410.

## Current Status

🟡 **Axiom-dependent** — The proof is complete with one citation axiom:

**Zsygmondy's Theorem** (K. Zsygmondy, 1892; Birkhoff–Vandiver, 1904): For a prime $p$ and $m \geq 7$, the number $p^m - 1$ has a primitive prime divisor $q$ — a prime such that $q \mid p^m - 1$ but $q \nmid p^i - 1$ for any $1 \leq i < m$. Moreover, $q \geq m + 1$.

```lean
axiom zsygmondy_prime_pow (p m : ℕ) (hp : p.Prime) (hm : 7 ≤ m) :
    ∃ q, q.Prime ∧ q ∣ p ^ m - 1 ∧ (∀ i, 1 ≤ i → i < m → ¬(q ∣ p ^ i - 1)) ∧ m + 1 ≤ q
```

**References:**
- K. Zsygmondy, "Zur Theorie der Potenzreste," *Monatsh. Math.* **3** (1892), 265–284.
- G. D. Birkhoff and H. S. Vandiver, "On the integral divisors of aⁿ − bⁿ," *Annals of Mathematics* **5** (1904), 173–180.

The axiom statement has been verified by a human against the Wikipedia article on Zsygmondy's theorem. The $m \geq 7$ bound avoids all known exceptions (the $(2, 6)$ case and Mersenne prime cases with $m = 2$).

## Goals

1. **Eliminate the Zsygmondy axiom** by proving it from first principles in Lean. This would promote the result from 🟡 axiom-dependent to 🟢 compiler-verified.
2. Once axiom-free, promote the finished proof to `botlib/NumberTheory/SmoothEscape.lean`.

## Files

- `Lean/SmoothEscape.lean` — Main proof (279 lines, 0 sorrys, 1 axiom)
- `Lean/Helpers.lean` — σ₁ growth bounds and orbit divergence
- `notes/smooth-escape-proof.md` — Verified NL proof

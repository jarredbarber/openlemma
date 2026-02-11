/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Nat.Prime.Basic

/-!
# Zsygmondy's Theorem (Citation Axiom)

Zsygmondy's theorem (1892): for `a > b ≥ 1` with `gcd(a,b) = 1` and `n ≥ 3`,
the number `aⁿ - bⁿ` has a prime factor that does not divide `aᵏ - bᵏ` for
any `1 ≤ k < n`, with finitely many exceptions.

This file states the special case `b = 1` (i.e., `pᵐ - 1` has a primitive
prime divisor for `m ≥ 7`), which avoids all known exceptions.

## Status

🔴 **AXIOM** — This is a citation axiom, not a proof. Proving this from
Mathlib primitives is an open formalization target.

The `m ≥ 7` bound is conservative and avoids:
- `2⁶ - 1 = 63 = 7 · 9` (Zsygmondy exception)
- Small cases where primitive divisors may not exist

## References

* K. Zsygmondy, "Zur Theorie der Potenzreste," Monatsh. Math. 3 (1892), 265–284.
* G. D. Birkhoff and H. S. Vandiver, "On the integral divisors of aⁿ − bⁿ,"
  Annals of Mathematics 5 (1904), 173–180.

## Proof sketch (for future formalization)

1. If `pᵐ - 1` has no primitive prime divisor, then every prime `q | pᵐ - 1`
   also divides `pᵈ - 1` for some `d | m` with `d < m`.
2. By the order of `p` modulo `q`: `ord_q(p) | m` and `ord_q(p) | d < m`,
   so `ord_q(p) | gcd(m, d)` which is a proper divisor of `m`.
3. This bounds `v_q(pᵐ - 1)` via lifting-the-exponent and shows
   `pᵐ - 1 ≤ ∏_{d | m, d < m} (pᵈ - 1)^{bounded}`, contradicting growth for large `m`.
-/

namespace OpenLemma.Zsygmondy

/-- **Zsygmondy's theorem** (special case `b = 1`):
For prime `p` and `m ≥ 7`, `pᵐ - 1` has a primitive prime divisor `q` that
does not divide `pⁱ - 1` for any `1 ≤ i < m`, and moreover `q ≥ m + 1`. -/
axiom zsygmondy_prime_pow (p m : ℕ) (hp : p.Prime) (hm : 7 ≤ m) :
    ∃ q, q.Prime ∧ q ∣ p ^ m - 1 ∧ (∀ i, 1 ≤ i → i < m → ¬(q ∣ p ^ i - 1)) ∧ m + 1 ≤ q

end OpenLemma.Zsygmondy

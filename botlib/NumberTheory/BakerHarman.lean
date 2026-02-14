/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.PrimeCounting

/-!
# Baker-Harman: Primes in Short Intervals

This file contains the statement of the Baker-Harman (1996) result on
primes in short intervals.

## Main Result

`baker_harman_short_intervals`: For α = 0.465, if x is sufficiently large
and x^(1-α) ≤ y ≤ x, then the interval (x, x+y] contains at least
C·y/log(x) primes for some absolute constant C > 0.

This is the current record (as of 1996) for the exponent in the short
intervals theorem. Any α < 1/2 would work for Konyagin's application,
but 0.465 is sharp.

## Reference

R. C. Baker, G. Harman, "The difference between consecutive primes,"
Proc. London Math. Soc. (3) 72 (1996), 261–280.

The proof uses sieve methods combined with Weil's bound for Kloosterman sums.
This is deep analytic number theory beyond the scope of elementary formalization.

## Usage

This theorem is used in Konyagin's proof (Theorem 1) to construct a large
set S of values u = w·p where w ≤ k^γ and p is prime in a short interval.
The Baker-Harman bound guarantees |S| ≥ c₁₁·k^(1-β) for appropriate choice
of parameters.

-/

/-- **Baker-Harman (1996): Primes in short intervals.**

For the exponent α = 0.465, there exist constants C > 0 and x₀ such that
for all x ≥ x₀ and all y with x^(1-α) ≤ y ≤ x, the number of primes in
the interval (x, x+y] is at least C·y/log(x).

More precisely: using 1 - α = 0.535, for y ≥ x^0.535, we have
π(x+y) - π(x) ≥ C·y/log(x).

**Proof sketch (beyond scope of formalization):**
1. Sieve methods to bound the error term in the prime number theorem
2. Weil bound for Kloosterman sums (from algebraic geometry over finite fields)
3. Vaughan's identity to separate main term from error
4. Careful optimization of parameters to reach α = 0.465

**Citation:** R. C. Baker, G. Harman, Proc. London Math. Soc. (3) 72 (1996),
261–280.

We axiomatize this result because:
- The proof is 20 pages of deep analytic number theory (sieves + Weil bound)
- Formalizing it would require significant algebraic geometry infrastructure
  (Kloosterman sums, character sums, Deligne's theorem)
- The result is standard and well-established
- Any α < 1/2 suffices for Konyagin's argument; the exact value 0.465 is
  not critical (even α = 0.49 would work)

**Note:** The Nat.primeCounting function counts primes up to and including n,
so primeCounting(x+y) - primeCounting(x) counts primes in (x, x+y]. -/
axiom baker_harman_short_intervals :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ (x : ℕ), x₀ ≤ x → ∀ (y : ℕ),
      (x : ℝ) ^ (0.535 : ℝ) ≤ y → (y : ℝ) ≤ x →
      C * y / Real.log x ≤ ((Nat.primeCounting (x + y)) - (Nat.primeCounting x) : ℝ)

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

/-!
# Konyagin's Theorem 2: Lattice Points Near Smooth Curves

This file contains the statement of Theorem 2 from Konyagin (1999),
which bounds the number of integer points near a smooth curve when
those points admit rational approximations with bounded denominators.

## Main Result

`konyagin_theorem2`: For a smooth function f on [0,N] with r-th derivative
bounded below by Dr and (r+1)-th derivative bounded above by Dr₁, if a set S
of integers has f(u) close to rationals v/w with denominator w ≤ W and
distance < δ, then |S| is bounded by a sum of three terms:
- (Dr·W²)^(1/(2r-1)) — from the lower bound on the r-th derivative
- (δ·W²/Dr)^(1/(r-1)) — from the approximation quality
- (Dr₁·W²/Dr)^(1/(2r)) — from the upper bound on the (r+1)-th derivative

## Reference

S. V. Konyagin, "Bounds on prime factors of consecutive integers,"
Mathematika 46 (1999), 41–55. Theorem 2, pages 48–51.

The proof uses Lemma 2 (small integer coefficients with vanishing conditions,
proved via Schmidt's rational subspace theory) combined with Taylor
approximation and a contradiction argument.

## Reusability

This theorem is a general tool for bounding integer solutions to
Diophantine inequalities |f(u) - v/w| < δ when f is smooth. It applies
beyond binomial coefficients to any smooth curve approximation problem.

-/

namespace Konyagin

/-- The constant c₁₀ from Theorem 2. Konyagin derives c₁₀ = 8e + 64c₉
where c₉ is from Lemma 2. For our purposes, any c_konyagin > 100 suffices
(the exact value doesn't matter for the asymptotic argument). -/
axiom c_konyagin : ℝ

axiom c_konyagin_pos : 0 < c_konyagin

axiom c_konyagin_large : 100 ≤ c_konyagin

/-- **Konyagin (1999), Theorem 2.**

For a C^(r+1) function f on [0,N] with:
- |f^(r)(u)| ≥ Dr for all u ∈ [0,N]
- |f^(r+1)(u)| ≤ Dr₁ for all u ∈ [0,N]

If S is a set of integers in [0,N] such that each u ∈ S admits a rational
approximation |f(u) - v/w| < δ with denominator w ≤ W, then:

|S| < c₁₀·N·((Dr·W²)^(1/(2r-1)) + (δ·W²/Dr)^(1/(r-1)) + (Dr₁·W²/Dr)^(1/(2r))) + 2r·lam

where lam ≥ 1 is a parameter (typically chosen as lam = 1 or a small constant).

**Proof sketch (Konyagin pages 48–51):**
1. Assume |S| is large. Pick 2r points u₁ < ... < u₂ᵣ from S.
2. Apply Lemma 2 to get small coefficients a₁,...,a₂ᵣ with polynomial
   vanishing up to degree r-1 and non-vanishing at degree r.
3. Form I = Σ aᵢwᵢf(uᵢ). By Taylor approximation around 0:
   - Main term I₁: degree-r part = (f^(r)(0)/r!) · Σ aᵢwᵢ(uᵢ choose r)
   - Remainder R: Taylor error + approximation error
4. I₁ is a nonzero integer (by Lemma 2's non-vanishing condition),
   so |I₁| ≥ Dr/2 for appropriate choice of point.
5. Bound |R| < |I₁| by choosing N small enough. This gives 0 < |I| < 1,
   contradicting I being an integer.
6. The three terms in the bound come from balancing N, W, δ to make this work.

**Citation:** S. V. Konyagin, Mathematika 46 (1999), Theorem 2.

We axiomatize this result rather than proving it because:
- The proof requires Schmidt's rational subspace theory (heights, successive
  minima, duality), which is deep Diophantine approximation not in Mathlib
- Theorem 2 is the right abstraction level: reusable beyond this application
- The ~1100 lines needed to formalize Lemma 2 + Schmidt's theory would be
  a one-off infrastructure build with no other use case

See `konyagin-formalization-plan.md` for detailed dependency analysis. -/
axiom konyagin_theorem2
    (r : ℕ) (hr : 1 ≤ r)
    (N W : ℝ) (hN : 0 < N) (hW : 1 ≤ W)
    (f : ℝ → ℝ) (hf_smooth : ContDiff ℝ (r + 1) f)
    (Dr Dr1 : ℝ) (hDr : 0 < Dr) (hDr1 : 0 < Dr1)
    (δ : ℝ) (hδ : 0 < δ)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hf_lower : ∀ u ∈ Set.Icc (0 : ℝ) N, Dr ≤ |iteratedDeriv r f u|)
    (hf_upper : ∀ u ∈ Set.Icc (0 : ℝ) N, |iteratedDeriv (r + 1) f u| ≤ Dr1)
    (S : Finset ℤ)
    (hS_range : ∀ u ∈ S, (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ N)
    (hS_approx : ∀ u ∈ S, ∃ v : ℤ, ∃ w : ℕ, 0 < w ∧ (w : ℝ) ≤ W ∧
                  |f u - v / w| < δ) :
    let term1 := (Dr * W^2) ^ (1 / (2*r - 1 : ℝ))
    let term2 := (δ * W^2 / Dr) ^ (1 / (r - 1 : ℝ))
    let term3 := (Dr1 * W^2 / Dr) ^ (1 / (2*r : ℝ))
    (S.card : ℝ) < c_konyagin * N * (term1 + term2 + term3) + 2 * r * lam

end Konyagin

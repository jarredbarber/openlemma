/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import problems.NumberTheory.Erdos1094.KLe28

/-!
# Erdős Problem 1094 — Main Theorem

The set of exceptions to `minFac(C(n,k)) ≤ max(n/k, k)` is finite,
contained in `{(n,k) : n < 285 ∧ k < 29}`.

## Axiom inventory (2 total, down from 5 + 1 sorry)
- `small_prime_kummer_density` — Kummer density bound, computationally verified for k ≤ 100000
  (used via `crt_density_from_asymptotic` in KGe29.lean)
- `large_n_smooth_case` — Sylvester-Schur type, pending librarian verification
-/

open Nat

namespace Erdos1094

theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite := by
  apply Set.Finite.subset (Set.Finite.prod (Set.finite_Iio 285) (Set.finite_Iio 29))
  intro ⟨n, k⟩ h
  simp only [Set.mem_setOf_eq] at h
  obtain ⟨hk_pos, h2k, hminFac⟩ := h
  simp only [Set.mem_prod, Set.mem_Iio]
  constructor
  · -- n < 285
    by_contra hn
    push_neg at hn
    have hk28 : k ≤ 28 := by
      by_contra hk
      push_neg at hk
      exact absurd (no_exception_k_ge_29 n k hk_pos h2k (by omega)) (by omega)
    exact absurd (bound_n_for_small_k n k hk_pos h2k hk28 (by omega)) (by omega)
  · -- k < 29
    by_contra hk
    push_neg at hk
    exact absurd (no_exception_k_ge_29 n k hk_pos h2k (by omega)) (by omega)

end Erdos1094

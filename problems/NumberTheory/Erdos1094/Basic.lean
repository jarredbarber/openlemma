/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import problems.NumberTheory.Erdos1094.KLe28

/-!
# Erdős Problem 1094 — Main Theorem

The set of exceptions to `minFac(C(n,k)) ≤ max(n/k, k)` is finite,
contained in `{(n,k) : n < 285 ∧ k < 29}`.

## What's proved vs conjectured

**Proved (compiler-verified, no axioms):**
- `card_KummerValid` — exact Kummer residue cardinality (Asymptotic.lean)
- `crt_verified_700` — exhaustive check for k ∈ [29, 700] (KGe29.lean, native_decide)
- `case_b_finite` — exhaustive check for k ∈ [17, 28], n ∈ [285, k²] (KLe28.lean)
- `large_n_minFac_bound` Type A — interval divisibility when n/k has large prime factor
- All arithmetic lemmas and wiring

**Axiom inventory (3 total, down from 5 + 1 sorry):**
1. `small_prime_kummer_density` (Asymptotic.lean) — density < 1/k², computationally verified
2. `crt_density_from_asymptotic` (KGe29.lean) — density→coverage bridge for k > 700
3. `large_n_smooth_case` (KGe29.lean) — smooth quotient case for n > k²

See KGe29.lean for detailed documentation of each axiom's status and evidence.
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

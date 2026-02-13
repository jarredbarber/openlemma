/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import problems.NumberTheory.Erdos1094.KLe28

/-!
# Erdős Problem 1094 — Main Theorem

The set of exceptions to `minFac(C(n,k)) ≤ max(n/k, k)` is finite.

## Proof structure

**n > k²:** `large_n_minFac_bound` (KGe29.lean) shows minFac(C(n,k)) ≤ n/k
for k ≥ 2. For k = 1: C(n,1) = n, minFac(n) ≤ n = max(n,1). Uses 1 axiom
(`large_n_smooth_case`).

**n ≤ k²:** Konyagin (1999) proves g(k) ≥ exp(c log²k), which exceeds k²
for large k (proved in `g_exceeds_k_sq`). So ∃ K₁ such that for k > K₁,
no exceptions exist in [k+2, k²]. For k ≤ K₁, the set is finite.
Uses 1 citation axiom (`konyagin_1999`).

## Axiom inventory (2 total)
1. `konyagin_1999` (Konyagin.lean) — citation: g(k) ≥ exp(c log²k)
2. `large_n_smooth_case` (KGe29.lean) — smooth quotient case for n > k²

## Axiom-free standalone results
- `small_prime_dvd_choose_of_le_sq` (AxiomFree.lean) — verified for k ∈ [2,700]
- `crt_verified_700` (KGe29.lean) — native_decide for k ∈ [29,700]
- `density_verified_700` (Asymptotic.lean) — density bound via native_decide
-/

open Nat

namespace Erdos1094

/-- **Erdős Problem 1094**: The set of exceptions to `minFac(C(n,k)) ≤ max(n/k, k)`
is finite. Uses 2 axioms: Konyagin (1999) citation and smooth-case conjecture. -/
theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite := by
  -- From Konyagin: ∃ K₁ such that ∀ k > K₁, g(k) > k² (no exceptions in [k+2, k²])
  obtain ⟨K₁, hK₁⟩ := g_exceeds_k_sq
  -- All exceptions have k ≤ K₁ (and therefore n ≤ K₁²)
  apply Set.Finite.subset
    (Set.Finite.prod (Set.finite_Iio (K₁ * K₁ + 1)) (Set.finite_Iio (K₁ + 1)))
  intro ⟨n, k⟩ hmem
  simp only [Set.mem_setOf_eq] at hmem
  obtain ⟨hk_pos, h2k, hminFac⟩ := hmem
  -- Step 1: n ≤ k² (otherwise large_n_minFac_bound gives minFac ≤ n/k ≤ max)
  have hn_sq : n ≤ k * k := by
    by_contra h
    push_neg at h
    rcases Nat.eq_or_lt_of_le hk_pos with rfl | hk2
    · -- k = 1: C(n,1) = n, minFac(n) ≤ n = max(n/1, 1)
      simp only [Nat.choose_one_right, Nat.div_one] at hminFac
      have : n.minFac ≤ n := Nat.minFac_le (by omega)
      have : n ≤ max n 1 := le_max_left _ _
      linarith
    · -- k ≥ 2: large_n_minFac_bound
      have := large_n_minFac_bound n k (by omega) h (by omega)
      exact absurd (le_trans this (le_max_left _ _)) (not_le.mpr hminFac)
  -- Step 2: k ≤ K₁ (otherwise Konyagin gives minFac ≤ k ≤ max)
  have hk_le : k ≤ K₁ := by
    by_contra hk
    push_neg at hk
    -- k ≥ 2 (from 2k ≤ n ≤ k²)
    have hk2 : 2 ≤ k := by nlinarith
    have hg := hK₁ k (by omega)
    have := no_exceptions_le_sq hg n (by omega) (by rwa [sq])
    exact absurd (le_trans this (le_max_right _ _)) (not_le.mpr hminFac)
  -- Conclude: (n, k) ∈ Iio(K₁² + 1) × Iio(K₁ + 1)
  simp only [Set.mem_prod, Set.mem_Iio]
  exact ⟨by nlinarith, by omega⟩

end Erdos1094

import Erdos.KLe28

open Nat

namespace Erdos1094

/--
For all n ≥ 2k the least prime factor of C(n,k) is ≤ max(n/k, k), with only
finitely many exceptions.

Reference: https://www.erdosproblems.com/1094
-/
theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite := by
  -- The exceptional set E is a subset of {(n,k) : n < 285 ∧ k < 29}, which is finite.
  -- Proof: if (n,k) ∈ E then k ≤ 28 (by contrapositive of no_exception_k_ge_29)
  -- and n ≤ 284 (by contrapositive of bound_n_for_small_k).
  apply Set.Finite.subset (Set.Finite.prod (Set.finite_Iio 285) (Set.finite_Iio 29))
  intro ⟨n, k⟩ h
  simp only [Set.mem_setOf_eq] at h
  obtain ⟨hk_pos, h2k, hminFac⟩ := h
  simp only [Set.mem_prod, Set.mem_Iio]
  constructor
  · -- Show n < 285 (i.e. n ≤ 284)
    by_contra hn
    push_neg at hn
    -- First establish k ≤ 28 (contrapositive of no_exception_k_ge_29)
    have hk28 : k ≤ 28 := by
      by_contra hk
      push_neg at hk
      exact absurd (no_exception_k_ge_29 n k hk_pos h2k (by omega)) (by omega)
    -- Then use bound_n_for_small_k to get a contradiction
    exact absurd (bound_n_for_small_k n k hk_pos h2k hk28 (by omega)) (by omega)
  · -- Show k < 29 (contrapositive of no_exception_k_ge_29)
    by_contra hk
    push_neg at hk
    exact absurd (no_exception_k_ge_29 n k hk_pos h2k (by omega)) (by omega)

end Erdos1094

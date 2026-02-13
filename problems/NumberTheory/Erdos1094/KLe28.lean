/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import botlib.NumberTheory.CarryInfra
import problems.NumberTheory.Erdos1094.KGe29

/-!
# No Exceptions for k ≤ 28 Beyond n = 284

For k ≤ 28, n > 284, and 2k ≤ n: `(n.choose k).minFac ≤ max (n/k) k`.

## Proof Structure

**k = 1:** C(n,1) = n, so minFac(n) ≤ n = max(n/1, 1).

**k ∈ [2, 16]:** k² ≤ 256 < 284 < n, so n > k². By `large_n_minFac_bound`,
minFac(C(n,k)) ≤ n/k ≤ max(n/k, k).

**k ∈ [17, 28]:** Split on n > k² (use `large_n_minFac_bound`) vs
284 < n ≤ k² (exhaustive native_decide).
-/

open Nat OpenLemma.CarryInfra

namespace Erdos1094

-- Finite verification: k ∈ [17, 28], n ∈ [285, k²].
set_option maxHeartbeats 2000000 in
set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
private lemma case_b_finite :
    ∀ k ∈ Finset.Icc 17 28, ∀ n ∈ Finset.Icc 285 (k * k),
    (n.choose k).minFac ≤ max (n / k) k := by native_decide

/-- No exceptions for k ≤ 28 beyond n = 284. -/
theorem bound_n_for_small_k (n k : ℕ) (hk : 0 < k) (hn : 2 * k ≤ n)
    (hk28 : k ≤ 28) (hn284 : 284 < n) :
    (n.choose k).minFac ≤ max (n / k) k := by
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · -- k = 1
    rw [Nat.choose_one_right, Nat.div_one]
    exact le_trans (Nat.minFac_le (by omega)) (le_max_left _ _)
  · by_cases hkk : k * k < n
    · -- n > k²: use large_n_minFac_bound
      exact le_trans (large_n_minFac_bound n k hk2 hkk (by omega))
                     (le_max_left _ _)
    · -- 284 < n ≤ k²: finite verification
      push_neg at hkk
      -- k ≤ 16 → k² ≤ 256 < 284 < n, contradiction
      have hk17 : 17 ≤ k := by nlinarith
      exact case_b_finite k (Finset.mem_Icc.mpr ⟨hk17, hk28⟩)
              n (Finset.mem_Icc.mpr ⟨by omega, hkk⟩)

end Erdos1094
